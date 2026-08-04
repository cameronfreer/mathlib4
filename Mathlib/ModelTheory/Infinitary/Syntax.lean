/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.ModelTheory.Syntax
public import Mathlib.ModelTheory.Infinitary.IndexCoding

/-!
# Infinitary first-order formulas

This file defines the syntax of `L_{∞ω}`: first-order formulas with conjunctions and
disjunctions indexed by a *fixed branching carrier* `ι`, one per formula. `L_{ω₁ω}` is the
definitional specialization `ι := ℕ`.

## Design

The infinitary constructors `iSup`/`iInf` branch over the single type parameter `ι` rather than
quantifying over a fresh index type at every node. Consequences:

- `BoundedFormulaInf L ι α n : Type (max u v u' uι)` — the syntax lives in the `max` of its
  parameters' universes, with no `+ 1` bump. In particular
  `BoundedFormulaω L α n := BoundedFormulaInf L ℕ α n` has exactly the universe
  `Type (max u v u')` of the finitary `BoundedFormula`.
- An `ι`-indexed conjunction at a larger carrier `κ` is expressed through an `IndexCoding`
  (`iInfAlong`/`iSupAlong`), padding undecodable branches with `⊤`/`⊥`; whole formulas are
  transported between carriers by `reindex`, which is functorial (`reindex_id`, `reindex_comp`)
  and semantics-preserving (`realize_reindex`, in `Infinitary/Semantics.lean`).
- Karp's theorem, the consumer that forces arbitrary index types, needs only the single carrier
  `M ⊕ N`: its `M`-indexed and `N`-indexed separating conjunctions are `iInfAlong` at the two
  sum codings.

## Main definitions

- `FirstOrder.Language.BoundedFormulaInf`: infinitary formulas with carrier `ι`, free variables
  in `α`, and `n` free *bound-variable* slots.
- `FirstOrder.Language.BoundedFormulaω`: the `ι := ℕ` specialization (an `abbrev`, so all
  `BoundedFormulaInf` API applies definitionally).
- `FirstOrder.Language.BoundedFormulaInf.iInfAlong`, `iSupAlong`: coded infinitary connectives.
- `FirstOrder.Language.BoundedFormulaInf.reindex`: carrier transport along an `IndexCoding`.
- `FirstOrder.Language.BoundedFormulaInf.toOmega`: recoding an encodable-carrier formula into
  `L_{ω₁ω}`.
-/

@[expose] public section

universe u v u' uι uκ uμ w

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

/-- An infinitary bounded formula of `L_{∞ω}`, with infinitary conjunctions and disjunctions
branching over the fixed carrier `ι`, free variables indexed by `α`, and `n` additional bound
variables available. -/
inductive BoundedFormulaInf (ι : Type uι) (α : Type u') : ℕ → Type (max u v u' uι) where
  /-- The false formula. -/
  | falsum {n} : BoundedFormulaInf ι α n
  /-- Equality of two terms. -/
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : BoundedFormulaInf ι α n
  /-- A relation symbol applied to terms. -/
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      BoundedFormulaInf ι α n
  /-- Implication. -/
  | imp {n} (φ ψ : BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n
  /-- Universal quantification over the last bound variable. -/
  | all {n} (φ : BoundedFormulaInf ι α (n + 1)) : BoundedFormulaInf ι α n
  /-- Infinitary disjunction over the carrier. -/
  | iSup {n} (φs : ι → BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n
  /-- Infinitary conjunction over the carrier. -/
  | iInf {n} (φs : ι → BoundedFormulaInf ι α n) : BoundedFormulaInf ι α n

/-- A bounded formula of `L_{ω₁ω}`: the definitional `ι := ℕ` specialization of
`BoundedFormulaInf`. Its universe is exactly that of the finitary `BoundedFormula`. -/
abbrev BoundedFormulaω (α : Type u') (n : ℕ) := L.BoundedFormulaInf ℕ α n

/-- An `L_{∞ω}` formula: a bounded formula with no free bound variables. -/
abbrev FormulaInf (ι : Type uι) (α : Type u') := L.BoundedFormulaInf ι α 0

/-- An `L_{∞ω}` sentence: a formula with no free variables at all. -/
abbrev SentenceInf (ι : Type uι) := L.FormulaInf ι Empty

/-- An `L_{ω₁ω}` formula. -/
abbrev Formulaω (α : Type u') := L.FormulaInf ℕ α

/-- An `L_{ω₁ω}` sentence. -/
abbrev Sentenceω := L.SentenceInf ℕ

variable {L} {ι : Type uι} {κ : Type uκ} {μ : Type uμ} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- The negation of an infinitary formula. -/
protected def not (φ : L.BoundedFormulaInf ι α n) : L.BoundedFormulaInf ι α n :=
  φ.imp .falsum

/-- The true formula. -/
protected def verum : L.BoundedFormulaInf ι α n :=
  BoundedFormulaInf.not .falsum

instance : Bot (L.BoundedFormulaInf ι α n) :=
  ⟨.falsum⟩

instance : Top (L.BoundedFormulaInf ι α n) :=
  ⟨BoundedFormulaInf.verum⟩

instance : Inhabited (L.BoundedFormulaInf ι α n) :=
  ⟨⊥⟩

/-- Existential quantification over the last bound variable. -/
protected def ex (φ : L.BoundedFormulaInf ι α (n + 1)) : L.BoundedFormulaInf ι α n :=
  φ.not.all.not

/-- An `ι`-indexed infinitary conjunction at carrier `κ`, along a coding: decoded indices
select their conjunct, undecodable ones are padded with `⊤`. -/
def iInfAlong (c : IndexCoding ι κ) (φs : ι → L.BoundedFormulaInf κ α n) :
    L.BoundedFormulaInf κ α n :=
  .iInf (c.pad ⊤ φs)

/-- An `ι`-indexed infinitary disjunction at carrier `κ`, along a coding: decoded indices
select their disjunct, undecodable ones are padded with `⊥`. -/
def iSupAlong (c : IndexCoding ι κ) (φs : ι → L.BoundedFormulaInf κ α n) :
    L.BoundedFormulaInf κ α n :=
  .iSup (c.pad ⊥ φs)

/-- Transport a formula along a coding of its carrier. Together with `reindex_id` and
`reindex_comp` this makes carrier transport functorial; `realize_reindex` (in
`Infinitary/Semantics.lean`) shows it is semantics-preserving. -/
def reindex (c : IndexCoding ι κ) : ∀ {n}, L.BoundedFormulaInf ι α n → L.BoundedFormulaInf κ α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal t₁ t₂
  | _, .rel R ts => .rel R ts
  | _, .imp φ ψ => (reindex c φ).imp (reindex c ψ)
  | _, .all φ => (reindex c φ).all
  | _, .iSup φs => iSupAlong c fun i ↦ reindex c (φs i)
  | _, .iInf φs => iInfAlong c fun i ↦ reindex c (φs i)

section ReindexEqs

variable (c : IndexCoding ι κ)

@[simp]
theorem reindex_falsum : reindex c (.falsum : L.BoundedFormulaInf ι α n) = .falsum :=
  rfl

@[simp]
theorem reindex_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    reindex c (.equal t₁ t₂ : L.BoundedFormulaInf ι α n) = .equal t₁ t₂ :=
  rfl

@[simp]
theorem reindex_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    reindex c (.rel R ts : L.BoundedFormulaInf ι α n) = .rel R ts :=
  rfl

@[simp]
theorem reindex_imp (φ ψ : L.BoundedFormulaInf ι α n) :
    reindex c (φ.imp ψ) = (reindex c φ).imp (reindex c ψ) :=
  rfl

@[simp]
theorem reindex_all (φ : L.BoundedFormulaInf ι α (n + 1)) :
    reindex c φ.all = (reindex c φ).all :=
  rfl

@[simp]
theorem reindex_iSup (φs : ι → L.BoundedFormulaInf ι α n) :
    reindex c (.iSup φs) = iSupAlong c fun i ↦ reindex c (φs i) :=
  rfl

@[simp]
theorem reindex_iInf (φs : ι → L.BoundedFormulaInf ι α n) :
    reindex c (.iInf φs) = iInfAlong c fun i ↦ reindex c (φs i) :=
  rfl

@[simp]
theorem reindex_not (φ : L.BoundedFormulaInf ι α n) :
    reindex c φ.not = (reindex c φ).not :=
  rfl

@[simp]
theorem reindex_ex (φ : L.BoundedFormulaInf ι α (n + 1)) :
    reindex c φ.ex = (reindex c φ).ex :=
  rfl

@[simp]
theorem reindex_top : reindex c (⊤ : L.BoundedFormulaInf ι α n) = ⊤ :=
  rfl

@[simp]
theorem reindex_bot : reindex c (⊥ : L.BoundedFormulaInf ι α n) = ⊥ :=
  rfl

end ReindexEqs

/-- Reindexing along the identity coding is syntactically the identity. -/
theorem reindex_id : ∀ {n} (φ : L.BoundedFormulaInf ι α n), reindex (.id ι) φ = φ := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => rw [reindex_imp, ihφ, ihψ]
  | all φ ih => rw [reindex_all, ih]
  | iSup φs ih => exact congrArg BoundedFormulaInf.iSup (funext fun i ↦ ih i)
  | iInf φs ih => exact congrArg BoundedFormulaInf.iInf (funext fun i ↦ ih i)

/-- Reindexing along a composite coding is the composite of the reindexings — syntactically,
not merely up to semantic equivalence. This is the coherence law that lets carrier transports
be chained. -/
theorem reindex_comp (c₂ : IndexCoding κ μ) (c₁ : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n),
      reindex (c₂.comp c₁) φ = reindex c₂ (reindex c₁ φ) := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => rw [reindex_imp, reindex_imp, reindex_imp, ihφ, ihψ]
  | all φ ih => rw [reindex_all, reindex_all, reindex_all, ih]
  | iSup φs ih =>
    refine congrArg BoundedFormulaInf.iSup (funext fun m ↦ ?_)
    change (c₂.comp c₁).pad ⊥ _ m = c₂.pad ⊥ _ m
    rcases h₂ : c₂.decode m with _ | k
    · have hc : (c₂.comp c₁).decode m = none := by simp [IndexCoding.comp, h₂]
      rw [(c₂.comp c₁).pad_of_decode_none hc, c₂.pad_of_decode_none h₂]
    · rcases h₁ : c₁.decode k with _ | i
      · have hc : (c₂.comp c₁).decode m = none := by simp [IndexCoding.comp, h₂, h₁]
        rw [(c₂.comp c₁).pad_of_decode_none hc, c₂.pad_of_decode_some h₂,
          c₁.pad_of_decode_none h₁, reindex_bot]
      · have hc : (c₂.comp c₁).decode m = some i := by simp [IndexCoding.comp, h₂, h₁]
        rw [(c₂.comp c₁).pad_of_decode_some hc, c₂.pad_of_decode_some h₂,
          c₁.pad_of_decode_some h₁, ih i]
  | iInf φs ih =>
    refine congrArg BoundedFormulaInf.iInf (funext fun m ↦ ?_)
    change (c₂.comp c₁).pad ⊤ _ m = c₂.pad ⊤ _ m
    rcases h₂ : c₂.decode m with _ | k
    · have hc : (c₂.comp c₁).decode m = none := by simp [IndexCoding.comp, h₂]
      rw [(c₂.comp c₁).pad_of_decode_none hc, c₂.pad_of_decode_none h₂]
    · rcases h₁ : c₁.decode k with _ | i
      · have hc : (c₂.comp c₁).decode m = none := by simp [IndexCoding.comp, h₂, h₁]
        rw [(c₂.comp c₁).pad_of_decode_none hc, c₂.pad_of_decode_some h₂,
          c₁.pad_of_decode_none h₁, reindex_top]
      · have hc : (c₂.comp c₁).decode m = some i := by simp [IndexCoding.comp, h₂, h₁]
        rw [(c₂.comp c₁).pad_of_decode_some hc, c₂.pad_of_decode_some h₂,
          c₁.pad_of_decode_some h₁, ih i]

/-- **Equivalence codings give genuine syntactic transport**: reindexing along an equivalence
and back is the identity, syntactically. Instantiated at `Equiv.ulift`, this is the
universe-lift operation on formulas together with its exact inverse — an arbitrary coding
preserves semantics but pads; an equivalence coding round-trips. -/
@[simp]
theorem reindex_ofEquiv_symm_reindex_ofEquiv (e : ι ≃ κ) (φ : L.BoundedFormulaInf ι α n) :
    reindex (.ofEquiv e.symm) (reindex (.ofEquiv e) φ) = φ := by
  rw [← reindex_comp, IndexCoding.ofEquiv_symm_comp, reindex_id]

/-- Recode a formula over an encodable carrier into `L_{ω₁ω}`. No choice is involved; for a
merely `Countable` carrier, obtain an `Encodable` instance via `Encodable.ofCountable` first.
This is the uniform, whole-formula conversion; the formula-sensitive conversion from an
`IsCountable` proof is `ofCountable` in `Infinitary/Countability.lean`. -/
def toOmega [Encodable ι] (φ : L.BoundedFormulaInf ι α n) : L.BoundedFormulaω α n :=
  reindex (.ofEncodable ι) φ

end BoundedFormulaInf

namespace BoundedFormula

/-- The embedding of finitary bounded formulas into the infinitary syntax. Since finitary
formulas have no infinitary nodes, the target carrier is arbitrary: there is one embedding for
all carriers and universes, rather than an embedding into `L_{ω₁ω}` followed by a lift. -/
def toInf : ∀ {n}, L.BoundedFormula α n → L.BoundedFormulaInf ι α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal t₁ t₂
  | _, .rel R ts => .rel R ts
  | _, .imp φ ψ => (toInf φ).imp (toInf ψ)
  | _, .all φ => (toInf φ).all

/-- The embedding of finitary bounded formulas into `L_{ω₁ω}`. -/
abbrev toOmega (φ : L.BoundedFormula α n) : L.BoundedFormulaω α n :=
  toInf φ

/-- Reindexing fixes the image of the finitary embedding: the finitary embedding at carrier
`κ` factors through ANY coding into `κ`. This replaces the embedding-triangle lemma of a
two-inductive design, and is syntactic. -/
@[simp]
theorem _root_.FirstOrder.Language.BoundedFormulaInf.reindex_toInf (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormula α n),
      BoundedFormulaInf.reindex c (toInf φ) = toInf φ := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => exact congrArg₂ BoundedFormulaInf.imp ihφ ihψ
  | all φ ih => exact congrArg BoundedFormulaInf.all ih

end BoundedFormula

end Language

end FirstOrder
