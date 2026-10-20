//! Polymorphic collection dictionaries use the ordinary notation-class route.
//! This is the pin's List.instAppend signature, not a special case for `++`.
use super::*;

pub(super) fn append(seed: &mut NumericSeed) -> Result<(), RecordError> {
    let u = Level::param(n("u"));
    let alpha = local("α", Expr::sort(succ(&u)?), BinderInfo::Implicit);
    let list = Expr::app(c("List", std::slice::from_ref(&u)), fv(&alpha));
    let value = Expr::app(c("List.append", std::slice::from_ref(&u)), fv(&alpha));
    seed.named_instance(
        "List.instAppend",
        &["u"],
        &[alpha],
        Expr::app(c("Append", std::slice::from_ref(&u)), list.clone()),
        app(c("Append.mk", &[u]), [list, value]),
        None,
    )
}
