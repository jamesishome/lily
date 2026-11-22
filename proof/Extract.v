From Stdlib Require Import extraction.ExtrOcamlBasic extraction.ExtrOcamlNatInt.
From Lily Require Bind.

Extract Inlined Constant Stdlib.Arith.PeanoNat.Nat.ltb => "(<)".

Extraction "model.ml"
  Bind.free Bind.well_scoped Bind.shift Bind.identity Bind.subst Bind.below
  Bind.weaken Bind.rename Bind.subst0.
