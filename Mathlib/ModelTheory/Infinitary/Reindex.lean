/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.ModelTheory.Infinitary.Semantics
public import Mathlib.ModelTheory.Infinitary.IndexCoding

/-!
# Carrier transport for infinitary formulas

Infinitary formulas fix one branching carrier per formula (`Infinitary/Syntax.lean`); this
file provides the transport layer between carriers, along `IndexCoding`s:

- `BoundedFormulaInf.iInfAlong`, `iSupAlong`: an `ι`-indexed conjunction/disjunction at a
  larger carrier `κ`, padding undecodable branches with `⊤`/`⊥` — semantically neutral
  (`realize_iInfAlong`, `realize_iSupAlong`).
- `BoundedFormulaInf.reindex`: whole-formula transport, functorial (`reindex_id`,
  `reindex_trans` — proved from the generic pad laws with no decoder analysis) and
  semantics-preserving (`realize_reindex`). Equivalence codings give genuine syntactic
  transport with an exact round trip (`reindexEquiv`); reindexing fixes the image of the
  finitary embedding (`reindex_toInf`), replacing the embedding triangle of a two-inductive
  design.
- `BoundedFormulaInf.toOmega`: recoding an encodable-carrier formula into `L_{ω₁ω}`.

Karp's theorem is the motivating consumer: its `M`-indexed and `N`-indexed separating
conjunctions are `iInfAlong` at the two sum codings into the single carrier `M ⊕ N`.
-/

@[expose] public section

universe u v u' uι uκ uμ w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι} {κ : Type uκ} {μ : Type uμ} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

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
`reindex_trans` this makes carrier transport functorial; `realize_reindex` (in
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
  | falsum | equal | rel => rfl
  | imp φ ψ ihφ ihψ => rw [reindex_imp, ihφ, ihψ]
  | all φ ih => rw [reindex_all, ih]
  | iSup φs ih => exact congrArg BoundedFormulaInf.iSup (funext ih)
  | iInf φs ih => exact congrArg BoundedFormulaInf.iInf (funext ih)

/-- The universal bound-variable closure commutes with carrier transport, syntactically. -/
@[simp]
theorem reindex_alls (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n), reindex c φ.alls = (reindex c φ).alls
  | 0, _ => rfl
  | _ + 1, φ => by
    change reindex c φ.all.alls = (reindex c φ).all.alls
    rw [reindex_alls, reindex_all]

/-- The existential bound-variable closure commutes with carrier transport, syntactically. -/
@[simp]
theorem reindex_exs (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n), reindex c φ.exs = (reindex c φ).exs
  | 0, _ => rfl
  | _ + 1, φ => by
    change reindex c φ.ex.exs = (reindex c φ).ex.exs
    rw [reindex_exs, reindex_ex]

/-- Reindexing along a composite coding is the composite of the reindexings — syntactically,
not merely up to semantic equivalence. This is the coherence law that lets carrier transports
be chained; it follows from the generic pad laws `IndexCoding.pad_trans` and
`IndexCoding.comp_pad`, with no decoder analysis. -/
theorem reindex_trans (c₁ : IndexCoding ι κ) (c₂ : IndexCoding κ μ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n),
      reindex (c₁.trans c₂) φ = reindex c₂ (reindex c₁ φ) := by
  intro n φ
  induction φ with
  | falsum | equal | rel => rfl
  | imp φ ψ ihφ ihψ => rw [reindex_imp, reindex_imp, reindex_imp, ihφ, ihψ]
  | all φ ih => rw [reindex_all, reindex_all, reindex_all, ih]
  | iSup φs ih =>
    simp only [reindex_iSup, iSupAlong, IndexCoding.pad_trans]
    congr 2
    rw [show (fun i ↦ reindex (c₁.trans c₂) (φs i)) =
      reindex c₂ ∘ fun i ↦ reindex c₁ (φs i) from funext ih]
    simpa only [reindex_bot] using
      (IndexCoding.comp_pad c₁ (reindex c₂) ⊥ (fun i ↦ reindex c₁ (φs i))).symm
  | iInf φs ih =>
    simp only [reindex_iInf, iInfAlong, IndexCoding.pad_trans]
    congr 2
    rw [show (fun i ↦ reindex (c₁.trans c₂) (φs i)) =
      reindex c₂ ∘ fun i ↦ reindex c₁ (φs i) from funext ih]
    simpa only [reindex_top] using
      (IndexCoding.comp_pad c₁ (reindex c₂) ⊤ (fun i ↦ reindex c₁ (φs i))).symm

/-- **Equivalence codings give genuine syntactic transport**: reindexing along an equivalence
and back is the identity, syntactically. Instantiated at `Equiv.ulift`, this is the
universe-lift operation on formulas together with its exact inverse — an arbitrary coding
preserves semantics but pads; an equivalence coding round-trips. -/
@[simp]
theorem reindex_ofEquiv_symm_reindex_ofEquiv (e : ι ≃ κ) (φ : L.BoundedFormulaInf ι α n) :
    reindex (.ofEquiv e.symm) (reindex (.ofEquiv e) φ) = φ := by
  rw [← reindex_trans, IndexCoding.ofEquiv_trans_ofEquiv_symm, reindex_id]

/-- Carrier equivalences are actual syntax equivalences. In particular
`reindexEquiv Equiv.ulift.symm` is the universe-lift operation on formulas, packaged with its
exact syntactic inverse. -/
def reindexEquiv (e : ι ≃ κ) : L.BoundedFormulaInf ι α n ≃ L.BoundedFormulaInf κ α n where
  toFun := reindex (.ofEquiv e)
  invFun := reindex (.ofEquiv e.symm)
  left_inv φ := reindex_ofEquiv_symm_reindex_ofEquiv e φ
  right_inv φ := by simpa using reindex_ofEquiv_symm_reindex_ofEquiv e.symm φ

/-- Recode a formula over an encodable carrier into `L_{ω₁ω}`. No choice is involved; for a
merely `Countable` carrier, obtain an `Encodable` instance via `Encodable.ofCountable` first.
This is the uniform, whole-formula conversion; the formula-sensitive conversion from an
`IsCountable` proof is `ofCountable` in `Infinitary/Countability.lean`. -/
def toOmega [Encodable ι] (φ : L.BoundedFormulaInf ι α n) : L.BoundedFormulaω α n :=
  reindex (.ofEncodable ι) φ

section Realize

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

/-- The `⊤`-padding of a coded conjunction is semantically neutral, generically in the
coding. -/
@[simp]
theorem realize_iInfAlong {c : IndexCoding ι κ} {φs : ι → L.BoundedFormulaInf κ α n} :
    (iInfAlong c φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [iInfAlong, realize_iInf]
  constructor
  · intro h i
    simpa only [IndexCoding.pad_encode] using h (c.encode i)
  · intro h k
    rcases hd : c.decode k with _ | i
    · simp only [c.pad_of_decode_none hd, realize_top]
    · simpa only [c.pad_of_decode_some hd] using h i

/-- The `⊥`-padding of a coded disjunction is semantically neutral, generically in the
coding. -/
@[simp]
theorem realize_iSupAlong {c : IndexCoding ι κ} {φs : ι → L.BoundedFormulaInf κ α n} :
    (iSupAlong c φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  simp only [iSupAlong, realize_iSup]
  constructor
  · rintro ⟨k, hk⟩
    rcases hd : c.decode k with _ | i
    · simp only [c.pad_of_decode_none hd, realize_bot] at hk
    · exact ⟨i, by simpa only [c.pad_of_decode_some hd] using hk⟩
  · rintro ⟨i, hi⟩
    exact ⟨c.encode i, by rwa [IndexCoding.pad_encode]⟩

/-- Carrier transport preserves realization. Being an iff, this transports semantic
equivalence in both directions as well. -/
@[simp]
theorem realize_reindex (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n) (v : α → M) (xs : Fin n → M),
      (reindex c φ).Realize v xs ↔ φ.Realize v xs := by
  intro n φ
  induction φ with
  | falsum | equal | rel => intro v xs; exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    intro v xs
    simpa only [reindex_imp, realize_imp] using imp_congr (ihφ v xs) (ihψ v xs)
  | all φ ih =>
    intro v xs
    simpa only [reindex_all, realize_all] using forall_congr' fun y ↦ ih v (Fin.snoc xs y)
  | iSup φs ih =>
    intro v xs
    simpa only [reindex_iSup, realize_iSupAlong] using exists_congr fun i ↦ ih i v xs
  | iInf φs ih =>
    intro v xs
    simpa only [reindex_iInf, realize_iInfAlong] using forall_congr' fun i ↦ ih i v xs

/-- Recoding an encodable-carrier formula into `L_{ω₁ω}` preserves realization. -/
@[simp]
theorem realize_toOmega [Encodable ι] (φ : L.BoundedFormulaInf ι α n) (v : α → M)
    (xs : Fin n → M) : (toOmega φ).Realize v xs ↔ φ.Realize v xs :=
  realize_reindex _ φ v xs

end Realize

end BoundedFormulaInf

/-- Reindexing fixes the image of the finitary embedding: the finitary embedding at carrier
`κ` factors through ANY coding into `κ`. This replaces the embedding-triangle lemma of a
two-inductive design, and is syntactic. -/
@[simp]
theorem BoundedFormulaInf.reindex_toInf (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormula α n),
      BoundedFormulaInf.reindex c (BoundedFormula.toInf φ) = BoundedFormula.toInf φ := by
  intro n φ
  induction φ with
  | falsum | equal | rel => rfl
  | imp φ ψ ihφ ihψ => exact congrArg₂ BoundedFormulaInf.imp ihφ ihψ
  | all φ ih => exact congrArg BoundedFormulaInf.all ih

end Language

end FirstOrder
