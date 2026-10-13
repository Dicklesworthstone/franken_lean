-- A named sort alias must not turn erased types into executable data.
def Universe : Type 1 := Type
axiom Carrier : Universe
axiom Family : Nat -> Universe
axiom secret : Nat

def carrierAlias : Universe := Carrier
def familyAlias : Nat -> Universe := Family
def takeType (T : Universe) : Nat := 7
def ordinary : Nat := takeType Carrier

noncomputable section
def hidden : Nat := secret
def successor : Nat := hidden + 1
end

theorem hidden_identity : hidden = secret := by rfl
