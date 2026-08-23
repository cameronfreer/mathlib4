import Mathlib.ModelTheory.Infinitary.QuantifierRank

/-!
# Acceptance probes for infinitary quantifier rank

The claims are about universe placement and transport, so they are checked by elaborating
statements rather than by proving anything new.
-/

universe u v u' uι uκ

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}

/-! ### The rank lands in the carrier's own ordinal universe -/

/-- Rank of an `ι`-branching formula is an `Ordinal.{uι}` — no bump, no lift. -/
noncomputable example {ι : Type uι} (φ : L.BoundedFormulaInf ι α n) : Ordinal.{uι} := φ.qrank

/-- The `L_{ω₁ω}` specialization lands in `Ordinal.{0}` EXACTLY, which is what Scott analysis
needs. Stated as an ascription so a silent `max`-bump would fail to elaborate. -/
noncomputable example (φ : L.BoundedFormulaω α n) : Ordinal.{0} := φ.qrank

/-- A carrier in the structure universe gives rank there. -/
noncomputable example {M : Type u} (φ : L.BoundedFormulaInf M α n) : Ordinal.{u} := φ.qrank

/-! ### Transport across `reindex` -/

example {ι : Type uι} {κ : Type uκ} (c : IndexCoding ι κ) (φ : L.BoundedFormulaInf ι α n) :
    Ordinal.lift.{uι} (BoundedFormulaInf.reindex c φ).qrank = Ordinal.lift.{uκ} φ.qrank :=
  BoundedFormulaInf.qrank_reindex c φ

/-- **Empty carrier**: every branch of the transported formula is padding, so this is the case
that would break if padding were not rank-neutral. -/
example {ι : Type uι} {κ : Type uκ} [IsEmpty ι] (c : IndexCoding ι κ)
    (φ : L.BoundedFormulaInf ι α n) :
    Ordinal.lift.{uι} (BoundedFormulaInf.reindex c φ).qrank = Ordinal.lift.{uκ} φ.qrank :=
  BoundedFormulaInf.qrank_reindex c φ

/-! ### Transport across an equivalence, including `ULift` -/

example {ι : Type uι} {κ : Type uκ} (e : ι ≃ κ) (φ : L.BoundedFormulaInf ι α n) :
    Ordinal.lift.{uι} (BoundedFormulaInf.reindex (.ofEquiv e) φ).qrank
      = Ordinal.lift.{uκ} φ.qrank :=
  BoundedFormulaInf.qrank_reindex_ofEquiv e φ

example {ι : Type uι} (φ : L.BoundedFormulaInf ι α n) :
    Ordinal.lift.{uι} (BoundedFormulaInf.reindex
        (.ofEquiv (Equiv.ulift.{uκ, uι}).symm) φ).qrank
      = Ordinal.lift.{max uι uκ} φ.qrank :=
  BoundedFormulaInf.qrank_reindex_ofEquiv _ φ

/-! ### `alls` / `exs` -/

example {ι : Type uι} (φ : L.BoundedFormulaInf ι α n) : φ.alls.qrank = φ.qrank + n :=
  BoundedFormulaInf.qrank_alls

example {ι : Type uι} (φ : L.BoundedFormulaInf ι α n) : φ.exs.qrank = φ.qrank + n :=
  BoundedFormulaInf.qrank_exs

/-! ### The finitary embedding is carrier-independent -/

example {ι : Type uι} {κ : Type uκ} (φ : L.BoundedFormula α n) :
    Ordinal.lift.{uκ} (BoundedFormula.toInf (ι := ι) φ).qrank
      = Ordinal.lift.{uι} (BoundedFormula.toInf (ι := κ) φ).qrank :=
  BoundedFormulaInf.qrank_toInf φ

end Language

end FirstOrder

/-! ### No countability, and no countability import

`assert_not_exists` fails if the named declaration IS in the environment, so this pins the
absence of the countability layer from this module's import cone. -/
assert_not_exists Cardinal.aleph
