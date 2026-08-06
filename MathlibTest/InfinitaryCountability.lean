import Mathlib.ModelTheory.Infinitary.Countability

/-!
Import-boundary probe for the intentionally opaque `ofCountable`: from outside its defining
module, construct it and reason exclusively through `realize_ofCountable` and
`ofCountable_proof_irrel`. The definition's body is not exposed — its syntactic output
depends on proof-directed encoding choices — so unfolding is neither available nor needed
here, and this file fails to elaborate if that public interface regresses.
-/

universe u v u' uι w

namespace FirstOrder.Language

open BoundedFormulaInf

example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    {ι : Type uι} {φ : L.BoundedFormulaInf ι α n} (h₁ h₂ : φ.IsCountable)
    (v : α → M) (xs : Fin n → M) :
    (ofCountable h₁).Realize v xs ↔ φ.Realize v xs := by
  rw [ofCountable_proof_irrel h₁ h₂]
  exact realize_ofCountable h₂

end FirstOrder.Language
