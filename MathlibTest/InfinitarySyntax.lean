import Mathlib.ModelTheory.Infinitary.Semantics
import Mathlib.ModelTheory.Infinitary.QuantifierRank
import Mathlib.ModelTheory.Infinitary.Countability

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
6. structural induction through the `BoundedFormulaω` abbreviation;
7. formula-sensitive countability — every formula is countable under `[Countable ι]`, the
   finitary embedding is countable and has index bound `0` at ARBITRARY (even uncountable)
   carriers with no carrier assumption, and the proof-directed `ofCountable` converts it to
   `BoundedFormulaω` with realization preserved;
8. equivalence codings round-trip syntactically — `reindex` genuinely replaces a `ULift`
   universe-lift operation, with an exact syntactic inverse;
9. the migration compatibility surface — seven qualified `BoundedFormulaω.*` constructor
   aliases suffice for source-level compatibility with code written against a dedicated
   `L_{ω₁ω}` inductive: they unfold by `rfl`, coexist with dot-notation, and no specialized
   recursor is needed.
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
`M`-indexed one (back) over the SAME formula type. These are `iInfAlong` at the two sum
codings; the padding is semantically neutral so the classical argument goes through verbatim.
The full theorem, proved against a genuine back-and-forth system, lives in the
`infinitary-logic` development; these probes reproduce its three load-bearing steps. -/

section Karp

variable {L : Language.{u, v}} {M N : Type w} [L.Structure M] [L.Structure N] {k : ℕ}

/-- Forth: a separating family indexed by `N` yields a formula true at `a`, witnessed by `m`. -/
example (a : Fin k → M) (m : M)
    (ψ : N → L.BoundedFormulaInf (M ⊕ N) (Fin k) 1)
    (hψ : ∀ j : N, (ψ j).Realize a (Fin.snoc Fin.elim0 m)) :
    (iInfAlong (.sumInr M N) ψ).ex.Realize a Fin.elim0 := by
  rw [realize_ex]
  exact ⟨m, by rw [realize_iInfAlong]; exact hψ⟩

/-- Back: the mirror, indexed by `M`, over the same formula type. -/
example (b : Fin k → N) (n' : N)
    (ψ : M → L.BoundedFormulaInf (M ⊕ N) (Fin k) 1)
    (hψ : ∀ i : M, (ψ i).Realize b (Fin.snoc Fin.elim0 n')) :
    (iInfAlong (.sumInl M N) ψ).ex.Realize b Fin.elim0 := by
  rw [realize_ex]
  exact ⟨n', by rw [realize_iInfAlong]; exact hψ⟩

/-- Refutation: if each conjunct fails at its own witness, the existential closure fails. -/
example (b : Fin k → N)
    (ψ : N → L.BoundedFormulaInf (M ⊕ N) (Fin k) 1)
    (hbad : ∀ y : N, ¬(ψ y).Realize b (Fin.snoc Fin.elim0 y)) :
    ¬(iInfAlong (.sumInr M N) ψ).ex.Realize b Fin.elim0 := by
  rw [realize_ex]
  rintro ⟨y, hy⟩
  rw [realize_iInfAlong] at hy
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

/-! ## 7. Formula-sensitive countability

The two notions kept distinct: "the carrier is countable" versus "this formula actually uses
an infinitary node." `Type` is an uncountable carrier at universe 1; the finitary embedding
into it must remain countable, convertible, and of index bound `0`. -/

section Countability

open BoundedFormulaInf

variable {L : Language.{u, v}} {α : Type u'} {M : Type w} [L.Structure M] {n : ℕ}
variable {v : α → M} {xs : Fin n → M}

/-- Under a countable carrier, every formula is countable — including infinitary ones. -/
example {ι : Type uι} [Countable ι] (φs : ι → L.BoundedFormulaInf ι α n) :
    (iInf φs).IsCountable :=
  isCountable_of_countable _

/-- The finitary embedding is countable at an UNCOUNTABLE carrier, with no assumption. -/
example (φ : L.BoundedFormula α n) : (φ.toInf (ι := Type)).IsCountable :=
  φ.isCountable_toInf

/-- A finitary formula at the uncountable carrier `Type` converts to `BoundedFormulaω` —
this is exactly where `toOmega` is unavailable (no `Encodable Type`). -/
noncomputable example (φ : L.BoundedFormula α n) : L.BoundedFormulaω α n :=
  ofCountable φ.isCountable_toInf (ι := Type)

/-- ...and the conversion preserves realization all the way back to the finitary formula. -/
example (φ : L.BoundedFormula α n) :
    (ofCountable (φ.isCountable_toInf (ι := Type))).Realize v xs ↔ φ.Realize v xs := by
  rw [BoundedFormulaInf.realize_ofCountable, BoundedFormula.realize_toInf]

/-- The index bound is formula-sensitive: `0` for the finitary embedding at an uncountable
carrier... -/
example (φ : L.BoundedFormula α n) : (φ.toInf (ι := Type)).indexBound = 0 :=
  φ.indexBound_toInf

/-- ...at most the carrier's cardinality for every formula... -/
example {ι : Type uι} (φ : L.BoundedFormulaInf ι α n) : φ.indexBound ≤ Cardinal.mk ι :=
  indexBound_le_mk φ

/-- ...and exactly the carrier's cardinality once an infinitary node occurs. -/
example {ι : Type uι} (φs : ι → L.BoundedFormulaInf ι α n) :
    (iInf φs).indexBound = Cardinal.mk ι :=
  indexBound_iInf

end Countability

/-! ## 8. Equivalence codings: syntactic round trip (the `liftUI` replacement) -/

section EquivRoundTrip

open BoundedFormulaInf

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}

/-- The round trip along any equivalence of carriers is the syntactic identity. -/
example {ι : Type uι} {κ : Type w} (e : ι ≃ κ) (φ : L.BoundedFormulaInf ι α n) :
    reindex (.ofEquiv e.symm) (reindex (.ofEquiv e) φ) = φ :=
  reindex_ofEquiv_symm_reindex_ofEquiv e φ

/-- Instantiated at `ULift`: lifting a formula's carrier to a higher universe and dropping
back down recovers the original formula syntactically — not merely semantically. This is the
universe-lift use case of the old two-inductive design, closed exactly. -/
example {ι : Type uι} (φ : L.BoundedFormulaInf ι α n) :
    reindex (.ofEquiv (Equiv.ulift.symm : ι ≃ ULift.{w} ι).symm)
      (reindex (.ofEquiv (Equiv.ulift.symm : ι ≃ ULift.{w} ι)) φ) = φ :=
  reindex_ofEquiv_symm_reindex_ofEquiv _ φ

end EquivRoundTrip

/-! ## 9. The `BoundedFormulaω` compatibility surface

Existing downstream code (76 files in the `infinitary-logic` repository) refers to qualified
constructor names such as `BoundedFormulaω.iInf`. This section checks that a seven-alias
compatibility namespace fully restores that surface over the abbreviation — and that no
generated-recursor compatibility (`rec`/`casesOn`) is needed, since induction and pattern
matching already work through the abbreviation (probed in section 6). -/

section OmegaCompat

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}

namespace BoundedFormulaω

/-- Compatibility alias for the qualified constructor name. -/
protected abbrev falsum : L.BoundedFormulaω α n :=
  BoundedFormulaInf.falsum

/-- Compatibility alias for the qualified constructor name. -/
protected abbrev equal (t₁ t₂ : L.Term (α ⊕ Fin n)) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.equal t₁ t₂

/-- Compatibility alias for the qualified constructor name. -/
protected abbrev rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    L.BoundedFormulaω α n :=
  BoundedFormulaInf.rel R ts

/-- Compatibility alias for the qualified constructor name. -/
protected abbrev imp (φ ψ : L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.imp φ ψ

/-- Compatibility alias for the qualified constructor name. -/
protected abbrev all (φ : L.BoundedFormulaω α (n + 1)) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.all φ

/-- Compatibility alias for the qualified constructor name. -/
protected abbrev iSup (φs : ℕ → L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.iSup φs

/-- Compatibility alias for the qualified constructor name. -/
protected abbrev iInf (φs : ℕ → L.BoundedFormulaω α n) : L.BoundedFormulaω α n :=
  BoundedFormulaInf.iInf φs

end BoundedFormulaω

/-- Representative downstream expressions compile against the aliases. -/
example (R : L.Relations 2) (ts : Fin 2 → L.Term (α ⊕ Fin n)) :
    L.BoundedFormulaω α n :=
  BoundedFormulaω.iInf fun _ ↦ BoundedFormulaω.imp (BoundedFormulaω.rel R ts)
    BoundedFormulaω.falsum

example (φ : L.BoundedFormulaω α (n + 1)) : L.BoundedFormulaω α n :=
  BoundedFormulaω.all φ

/-- The aliases unfold to the underlying constructors by `rfl`. -/
example (φs : ℕ → L.BoundedFormulaω α n) :
    BoundedFormulaω.iInf φs = BoundedFormulaInf.iInf φs :=
  rfl

example : (BoundedFormulaω.falsum : L.BoundedFormulaω α n) = BoundedFormulaInf.falsum :=
  rfl

/-- Dot-notation still elaborates alongside the aliases. -/
example (φs : ℕ → L.BoundedFormulaω α 0) : L.BoundedFormulaω α 0 :=
  .iInf φs

/-- Induction on an alias-built formula still exposes the seven underlying cases; no
specialized recursor is required. -/
example {M : Type w} [L.Structure M] (φs : ℕ → L.BoundedFormulaω α n)
    (v : α → M) (xs : Fin n → M) :
    (BoundedFormulaω.iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  induction h : BoundedFormulaω.iInf φs with
  | iInf φs' ih => simp_all [BoundedFormulaInf.realize_iInf]
  | falsum | equal | rel | imp | all | iSup => simp_all

end OmegaCompat

end FirstOrder.Language
