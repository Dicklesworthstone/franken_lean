//! Reconstruct checked metadata and defer Handle terminal observations.
//!
//! Packed native integers, words and records never masquerade as logical
//! Int/UInt32/UInt64/SystemTime/Metadata values. Only the validated private
//! transport supplies scalar fields to the separately checked constructors.
use super::*;

const NATIVE_METADATA: &str = "_fln_runtime_fs_metadata_payload";

#[derive(Clone)]
struct WordLayout {
    word: Name,
    bits: Name,
    fin: Name,
}

#[derive(Clone)]
pub(super) struct Layout {
    native: Expr,
    integer: records::Shape,
    word32: WordLayout,
    word64: WordLayout,
    file_type: records::Shape,
    time: records::ShapeConstructor,
    metadata: records::ShapeConstructor,
}

fn constructor(shape: &records::ShapeConstructor, fields: impl IntoIterator<Item = Expr>) -> Expr {
    apply(Expr::const_(shape.name.clone(), Vec::new()), fields)
}

fn word(layout: &WordLayout, value: Expr) -> Expr {
    let finite = apply(
        Expr::const_(layout.fin.clone(), Vec::new()),
        [value, proofs::erased_value()],
    );
    Expr::app(
        Expr::const_(layout.word.clone(), Vec::new()),
        Expr::app(Expr::const_(layout.bits.clone(), Vec::new()), finite),
    )
}

impl Preparation<'_> {
    fn fs_metadata_word(&mut self, type_: Expr) -> Result<WordLayout, IngressError> {
        let word = self.io_checked_single_constructor(type_, 1)?;
        let bits = self.io_checked_single_constructor(word.fields[0].clone(), 1)?;
        let finite = self.io_checked_single_constructor(bits.fields[0].clone(), 2)?;
        if finite.fields != [c("Nat"), proofs::erased_type()] {
            return Err(unsupported("metadata checked finite word layout"));
        }
        Ok(WordLayout {
            word: word.name,
            bits: bits.name,
            fin: finite.name,
        })
    }

    fn fs_metadata_layout(&mut self) -> Result<Layout, IngressError> {
        if let Some(layout) = &self.fs.metadata {
            return Ok(layout.clone());
        }
        let integer = self.io_checked_shape(c("Int"))?;
        if integer.constructors.len() != 2
            || integer
                .constructors
                .iter()
                .enumerate()
                .any(|(index, ctor)| ctor.tag != index as u8 || ctor.fields != [c("Nat")])
        {
            return Err(unsupported("metadata checked signed seconds layout"));
        }
        let word32 = self.fs_metadata_word(c("UInt32"))?;
        let word64 = self.fs_metadata_word(c("UInt64"))?;
        let file_type = self.io_checked_shape(c("IO.FS.FileType"))?;
        if file_type.constructors.len() != 4
            || file_type
                .constructors
                .iter()
                .enumerate()
                .any(|(index, ctor)| ctor.tag != index as u8 || !ctor.fields.is_empty())
        {
            return Err(unsupported("metadata checked file type layout"));
        }
        let time = self.io_checked_single_constructor(c("IO.FS.SystemTime"), 2)?;
        let metadata = self.io_checked_single_constructor(c("IO.FS.Metadata"), 5)?;
        if time.fields != [c("Int"), c("UInt32")]
            || metadata.fields
                != [
                    c("IO.FS.SystemTime"),
                    c("IO.FS.SystemTime"),
                    c("UInt64"),
                    c("IO.FS.FileType"),
                    c("UInt64"),
                ]
        {
            return Err(unsupported("metadata checked record layout"));
        }
        let native = self.io_private_record(
            NATIVE_METADATA,
            vec![
                c("Bool"),
                c("Nat"),
                c("Nat"),
                c("Bool"),
                c("Nat"),
                c("Nat"),
                c("Nat"),
                c("Nat"),
                c("Nat"),
            ],
        )?;
        let layout = Layout {
            native,
            integer,
            word32,
            word64,
            file_type,
            time,
            metadata,
        };
        self.fs.metadata = Some(layout.clone());
        Ok(layout)
    }

    pub(super) fn fs_materialize_metadata(&mut self, payload: Expr) -> Result<Expr, IngressError> {
        let layout = self.fs_metadata_layout()?;
        let field = |index| Ok::<_, IngressError>(Expr::proj(name(NATIVE_METADATA), index, b(0)?));
        let timestamp = |offset| -> Result<Expr, IngressError> {
            let seconds = choose(
                layout.integer.source.clone(),
                field(offset)?,
                constructor(&layout.integer.constructors[0], [field(offset + 1)?]),
                constructor(&layout.integer.constructors[1], [field(offset + 1)?]),
            );
            Ok(constructor(
                &layout.time,
                [seconds, word(&layout.word32, field(offset + 2)?)],
            ))
        };
        // The safe producer bounds the ordinal to 0..=3. Branches are checked
        // logical constructors; no packed runtime tag is reinterpreted.
        let mut file_type = constructor(&layout.file_type.constructors[3], []);
        for index in (0..3).rev() {
            self.tick()?;
            file_type = choose(
                layout.file_type.source.clone(),
                apply(c("Nat.beq"), [field(7)?, nat::literal(index as u64)]),
                file_type,
                constructor(&layout.file_type.constructors[index], []),
            );
        }
        let value = constructor(
            &layout.metadata,
            [
                timestamp(0)?,
                timestamp(3)?,
                word(&layout.word64, field(6)?),
                file_type,
                word(&layout.word64, field(8)?),
            ],
        );
        Ok(Expr::let_e(
            self.fs_adapter_name()?,
            layout.native,
            payload,
            value,
            false,
        ))
    }

    pub(super) fn fs_is_tty_call(
        &mut self,
        arguments: &[Expr],
        layout: &super::Layout,
        primitive: Name,
    ) -> Result<Expr, IngressError> {
        let result = self.io_checked_shape(apply(c("ST.Out"), [c("IO.RealWorld"), c("Bool")]))?;
        if result.constructors.len() != 1
            || result.constructors[0].tag != 0
            || result.constructors[0].fields != [c("Bool"), layout.world.clone()]
        {
            return Err(unsupported("terminal checked BaseIO result layout"));
        }
        let returned = constructor(&result.constructors[0], [b(0)?, b(1)?]);
        // At the native call #0 is world and #1 is Handle. The strict Bool
        // binding is inside the world lambda, so aliases and partial calls
        // keep their reusable action and do not observe the descriptor early.
        let mut body = Expr::let_e(
            self.fs_adapter_name()?,
            c("Bool"),
            Expr::app(Expr::const_(primitive, Vec::new()), b(1)?),
            returned,
            false,
        );
        let domains = [layout.receiver.clone(), layout.world.clone()];
        for domain in domains.iter().rev() {
            body = Expr::lam(
                self.fs_adapter_name()?,
                domain.clone(),
                body,
                BinderInfo::Default,
            );
        }
        let wrapper = Expr::let_e(
            self.fs_adapter_name()?,
            function(&domains, result.source),
            body,
            b(0)?,
            false,
        );
        Ok(arguments.iter().cloned().fold(wrapper, Expr::app))
    }
}
