import Mathlib.ModelTheory.Infinitary.Reindex

/-!
Regression probes for the carrier-transport layer. Each example fails to elaborate if the
design regresses: the empty carrier must recode with no hidden `Nonempty` assumption, an
equivalence coding must round-trip syntactically (the `ULift` instance is the universe-lift
operation with its exact inverse), and an explicitly given encoding must be consumed as data,
not found by instance search.
-/

universe u v u' uι w

namespace FirstOrder.Language

open BoundedFormulaInf

/-- Empty-carrier recoding: the empty conjunction recodes into `L_{ω₁ω}` and is vacuously
realized — no hidden `Nonempty` assumption anywhere in the coding path. -/
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    {v : α → M} {xs : Fin n → M} (φs : Empty → L.BoundedFormulaInf Empty α n) :
    (toOmega (.iInf φs)).Realize v xs := by
  rw [realize_toOmega, realize_iInf]
  exact fun i ↦ i.elim

/-- The syntactic round trip along an equivalence coding, at `ULift`: lifting a formula's
carrier to a higher universe and dropping back recovers the formula syntactically. -/
example {L : Language.{u, v}} {α : Type u'} {n : ℕ} {ι : Type uι}
    (φ : L.BoundedFormulaInf ι α n) :
    reindex (.ofEquiv (Equiv.ulift.symm : ι ≃ ULift.{w} ι).symm)
      (reindex (.ofEquiv (Equiv.ulift.symm : ι ≃ ULift.{w} ι)) φ) = φ :=
  reindex_ofEquiv_symm_reindex_ofEquiv _ φ

/-- Reindexing fixes the image of the carrier-generic finitary embedding. -/
example {L : Language.{u, v}} {α : Type u'} {n : ℕ} {ι : Type uι} {κ : Type w}
    (c : IndexCoding ι κ) (φ : L.BoundedFormula α n) :
    BoundedFormulaInf.reindex c (BoundedFormula.toInf φ) = BoundedFormula.toInf φ :=
  BoundedFormulaInf.reindex_toInf c φ

/-- Explicit stored encodings: no `[Encodable ι]` instance is in scope — the coding consumes
only the given value `e`, as data-carrying coded presentations require. -/
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    {ι : Type uι} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n)
    (v : α → M) (xs : Fin n → M) :
    (iInfAlong (.ofEncodableWith e) φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  realize_iInfAlong

end FirstOrder.Language
