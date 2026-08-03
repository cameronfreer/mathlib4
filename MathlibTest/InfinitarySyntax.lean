import Mathlib.ModelTheory.Infinitary.Semantics
import Mathlib.ModelTheory.Infinitary.QuantifierRank

/-!
# Acceptance probes for the carrier-parameterized infinitary syntax

These examples are the falsification gates for the design decision that infinitary formulas fix
ONE branching carrier `ι` per formula (rather than quantifying over a fresh index type at every
`iSup`/`iInf` node). Each probe is stated so that it fails to elaborate if the design regresses:

1. universes — no `+ 1` bump, and the `ι := ℕ` specialization matches the finitary
   `BoundedFormula` universe exactly;
2. the realization lemmas apply by `simp only` (not by definitional unfolding) at a literal
   nonzero index universe;
3. the Karp shape — `M`- and `N`-indexed separating conjunctions at the single carrier
   `M ⊕ N`, with semantically neutral padding;
4. `Encodable` recoding into `L_{ω₁ω}`, including the empty carrier (no hidden `Nonempty`);
5. quantifier-rank transport under recoding, including at the empty carrier;
6. structural induction through the `BoundedFormulaω` abbreviation.
-/

universe u v u' uι w

namespace FirstOrder.Language

open BoundedFormulaInf

/-! ## 1. Universe probes: the assertions ARE the types -/

/-- The syntax lives at `max` of its parameters' universes: no bump. -/
example (L : Language.{u, v}) (ι : Type uι) (α : Type u') (n : ℕ) :
    Type (max u v u' uι) :=
  L.BoundedFormulaInf ι α n

/-- The `ι := ℕ` specialization has EXACTLY the finitary `BoundedFormula` universe. -/
example (L : Language.{u, v}) (α : Type u') (n : ℕ) : Type (max u v u') :=
  L.BoundedFormulaω α n

/-- Carrier at a literal nonzero universe. -/
example (L : Language.{u, v}) (α : Type u') : Type (max u v u' 1) :=
  L.BoundedFormulaInf (Type 0) α 0

/-- Carrier at an arbitrary structure universe: the Karp shape. -/
example (L : Language.{u, v}) (M N : Type w) (α : Type u') : Type (max u v u' w) :=
  L.BoundedFormulaInf (M ⊕ N) α 0

/-! ## 2. Realization by `simp only` at a literal nonzero index universe -/

example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    {ι : Type 1} (φs : ι → L.BoundedFormulaInf ι α n) (v : α → M) (xs : Fin n → M) :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [realize_iInf]

example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
    {ι : Type uι} (φs : ι → L.BoundedFormulaInf ι α n) (v : α → M) (xs : Fin n → M) :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  simp only [realize_iSup]

/-! ## 3. The Karp shape at the single carrier `M ⊕ N`

The backward direction of Karp's theorem needs an `N`-indexed conjunction (forth) and an
`M`-indexed one (back) over the SAME formula type. These are `codediInf` at the two sum
codings; the padding is semantically neutral so the classical argument goes through verbatim.
The full theorem, proved against a genuine back-and-forth system, lives in the
`infinitary-logic` development; these probes reproduce its three load-bearing steps. -/

section Karp

variable {L : Language.{u, v}} {M N : Type w} [L.Structure M] [L.Structure N] {k : ℕ}

/-- Forth: a separating family indexed by `N` yields a formula true at `a`, witnessed by `m`. -/
example (a : Fin k → M) (m : M)
    (ψ : N → L.BoundedFormulaInf (M ⊕ N) (Fin k) 1)
    (hψ : ∀ j : N, (ψ j).Realize a (Fin.snoc Fin.elim0 m)) :
    (codediInf (.sumInr M N) ψ).ex.Realize a Fin.elim0 := by
  rw [realize_ex]
  exact ⟨m, by rw [realize_codediInf]; exact hψ⟩

/-- Back: the mirror, indexed by `M`, over the same formula type. -/
example (b : Fin k → N) (n' : N)
    (ψ : M → L.BoundedFormulaInf (M ⊕ N) (Fin k) 1)
    (hψ : ∀ i : M, (ψ i).Realize b (Fin.snoc Fin.elim0 n')) :
    (codediInf (.sumInl M N) ψ).ex.Realize b Fin.elim0 := by
  rw [realize_ex]
  exact ⟨n', by rw [realize_codediInf]; exact hψ⟩

/-- Refutation: if each conjunct fails at its own witness, the existential closure fails. -/
example (b : Fin k → N)
    (ψ : N → L.BoundedFormulaInf (M ⊕ N) (Fin k) 1)
    (hbad : ∀ y : N, ¬(ψ y).Realize b (Fin.snoc Fin.elim0 y)) :
    ¬(codediInf (.sumInr M N) ψ).ex.Realize b Fin.elim0 := by
  rw [realize_ex]
  rintro ⟨y, hy⟩
  rw [realize_codediInf] at hy
  exact hbad y (hy y)

end Karp

/-! ## 4. `Encodable` recoding into `L_{ω₁ω}` -/

section Recoding

variable {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
variable {v : α → M} {xs : Fin n → M}

/-- The empty carrier recodes with no hidden `Nonempty` assumption: the empty conjunction is
vacuously realized after recoding. -/
example (φs : Empty → L.BoundedFormulaInf Empty α n) :
    (toOmega (.iInf φs)).Realize v xs := by
  rw [realize_toOmega, realize_iInf]
  exact fun i ↦ i.elim

/-- Finite carriers recode with realization preserved. -/
example {k : ℕ} (φs : Fin k → L.BoundedFormulaInf (Fin k) α n) :
    (toOmega (.iInf φs)).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  rw [realize_toOmega, realize_iInf]

/-- The `Countable` corollary: choice produces the encoding, the coding itself does not use
it. -/
noncomputable example {ι : Type uι} [Countable ι] (φ : L.BoundedFormulaInf ι α n) :
    { ψ : L.BoundedFormulaω α n //
      ∀ (Q : Type w) [L.Structure Q] (v : α → Q) (xs : Fin n → Q),
        ψ.Realize v xs ↔ φ.Realize v xs } := by
  haveI : Encodable ι := Encodable.ofCountable ι
  exact ⟨toOmega φ, fun Q _ v xs ↦ realize_toOmega φ v xs⟩

end Recoding

/-! ## 5. Quantifier rank: universe placement and transport -/

/-- At the `ℕ` carrier the rank lands in `Ordinal.{0}`, where Scott analysis needs it. -/
noncomputable example {L : Language.{u, v}} {α : Type u'} (φ : L.BoundedFormulaω α 0) :
    Ordinal.{0} :=
  φ.qrank

/-- At a structure carrier the rank lives in that carrier's universe. -/
noncomputable example {L : Language.{u, v}} {α : Type u'} {M N : Type w}
    (φ : L.BoundedFormulaInf (M ⊕ N) α 0) : Ordinal.{w} :=
  φ.qrank

/-- Rank transport at the empty carrier: the empty supremum survives recoding. -/
example {L : Language.{u, v}} {α : Type u'}
    (φs : Empty → L.BoundedFormulaInf Empty α 0) :
    Ordinal.lift.{0} (toOmega (.iInf φs)).qrank = Ordinal.lift.{0} (iInf φs).qrank :=
  qrank_reindex _ _

/-! ## 6. Structural induction through the abbreviation -/

/-- `BoundedFormulaω` still yields all seven cases with `ℕ`-indexed induction hypotheses. -/
example {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {k : ℕ}
    (φ : L.BoundedFormulaω α k) (v : α → M) (xs : Fin k → M) :
    φ.Realize v xs ∨ ¬φ.Realize v xs := by
  induction φ with
  | falsum => exact Or.inr (by simp)
  | equal => exact Classical.em _
  | rel => exact Classical.em _
  | imp => exact Classical.em _
  | all => exact Classical.em _
  | iSup φs ih => exact Classical.em _
  | iInf φs ih => exact Classical.em _

/-- Constructor dot-notation elaborates at the `ℕ` specialization. -/
example {L : Language.{u, v}} {α : Type u'} (φs : ℕ → L.BoundedFormulaω α 0) :
    L.BoundedFormulaω α 0 :=
  .iInf φs

end FirstOrder.Language
