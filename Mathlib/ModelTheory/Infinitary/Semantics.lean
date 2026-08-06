/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.Infinitary.Syntax

/-!
# Semantics of infinitary first-order formulas

This file defines realization of `L_{∞ω}` formulas in a structure, with simp lemmas for every
constructor and derived connective. Because the branching carrier is a type parameter, each
realization lemma is a single statement generic in the carrier and its universe — there is no
separate `L_{ω₁ω}` semantics, and no universe-specialized lemma set.

## Main definitions

- `FirstOrder.Language.BoundedFormulaInf.Realize`: realization with free-variable and
  bound-variable valuations.
- `FirstOrder.Language.FormulaInf.Realize`, `FirstOrder.Language.SentenceInf.Realize`.

## Main statements

- `realize_iInfAlong`, `realize_iSupAlong`: the `⊤`/`⊥` padding of the coded connectives is
  semantically neutral, generically in the coding.
- `realize_reindex`: carrier transport preserves realization (in both directions, being an
  iff), hence also semantic equivalence.
- `realize_toOmega`, `BoundedFormula.realize_toInf`: the recoding into `L_{ω₁ω}` and the
  finitary embedding preserve realization.
-/

@[expose] public section

universe u v u' uι uκ w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {ι : Type uι} {κ : Type uκ} {α : Type u'} {n : ℕ}

namespace BoundedFormulaInf

/-- Realization of an infinitary bounded formula in a structure, given valuations of the free
and bound variables. One recursion serves every carrier. -/
def Realize {M : Type w} [L.Structure M] :
    ∀ {n}, L.BoundedFormulaInf ι α n → (α → M) → (Fin n → M) → Prop
  | _, .falsum, _, _ => False
  | _, .equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, .rel R ts, v, xs => Structure.RelMap R fun i ↦ (ts i).realize (Sum.elim v xs)
  | _, .imp φ ψ, v, xs => Realize φ v xs → Realize ψ v xs
  | _, .all φ, v, xs => ∀ y : M, Realize φ v (Fin.snoc xs y)
  | _, .iSup φs, v, xs => ∃ i, Realize (φs i) v xs
  | _, .iInf φs, v, xs => ∀ i, Realize (φs i) v xs

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

@[simp]
theorem realize_falsum : (falsum : L.BoundedFormulaInf ι α n).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_equal {t₁ t₂ : L.Term (α ⊕ Fin n)} :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).Realize v xs ↔
      t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_rel {l : ℕ} {R : L.Relations l} {ts : Fin l → L.Term (α ⊕ Fin n)} :
    (rel R ts : L.BoundedFormulaInf ι α n).Realize v xs ↔
      Structure.RelMap R fun i ↦ (ts i).realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_imp {φ ψ : L.BoundedFormulaInf ι α n} :
    (φ.imp ψ).Realize v xs ↔ φ.Realize v xs → ψ.Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_all {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.all.Realize v xs ↔ ∀ y : M, φ.Realize v (Fin.snoc xs y) :=
  Iff.rfl

/-- Realization of an infinitary disjunction: one equation, generic in the carrier and its
universe. -/
@[simp]
theorem realize_iSup {φs : ι → L.BoundedFormulaInf ι α n} :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  Iff.rfl

/-- Realization of an infinitary conjunction: one equation, generic in the carrier and its
universe. -/
@[simp]
theorem realize_iInf {φs : ι → L.BoundedFormulaInf ι α n} :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_not {φ : L.BoundedFormulaInf ι α n} :
    φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.BoundedFormulaInf ι α n).Realize v xs ↔ True := by
  simp [Top.top, BoundedFormulaInf.verum, BoundedFormulaInf.not, Realize]

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormulaInf ι α n).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_ex {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.ex.Realize v xs ↔ ∃ y : M, φ.Realize v (Fin.snoc xs y) := by
  simp only [BoundedFormulaInf.ex, realize_not, realize_all, not_forall, not_not]

/-- The `⊤`-padding of a coded conjunction is semantically neutral, generically in the
coding. -/
@[simp]
theorem realize_iInfAlong {c : IndexCoding ι κ} {φs : ι → L.BoundedFormulaInf κ α n} :
    (iInfAlong c φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [iInfAlong, realize_iInf]
  constructor
  · intro h i
    have hi := h (c.encode i)
    rwa [IndexCoding.pad_encode] at hi
  · intro h k
    rcases hd : c.decode k with _ | i
    · rw [c.pad_of_decode_none hd]
      simp
    · rw [c.pad_of_decode_some hd]
      exact h i

/-- The `⊥`-padding of a coded disjunction is semantically neutral, generically in the
coding. -/
@[simp]
theorem realize_iSupAlong {c : IndexCoding ι κ} {φs : ι → L.BoundedFormulaInf κ α n} :
    (iSupAlong c φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  simp only [iSupAlong, realize_iSup]
  constructor
  · rintro ⟨k, hk⟩
    rcases hd : c.decode k with _ | i
    · rw [c.pad_of_decode_none hd] at hk
      simp at hk
    · rw [c.pad_of_decode_some hd] at hk
      exact ⟨i, hk⟩
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
  | falsum => intro v xs; exact Iff.rfl
  | equal t₁ t₂ => intro v xs; exact Iff.rfl
  | rel R ts => intro v xs; exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    intro v xs
    simp only [reindex_imp, realize_imp]
    exact imp_congr (ihφ v xs) (ihψ v xs)
  | all φ ih =>
    intro v xs
    simp only [reindex_all, realize_all]
    exact forall_congr' fun y ↦ ih v (Fin.snoc xs y)
  | iSup φs ih =>
    intro v xs
    simp only [reindex_iSup, realize_iSupAlong]
    exact exists_congr fun i ↦ ih i v xs
  | iInf φs ih =>
    intro v xs
    simp only [reindex_iInf, realize_iInfAlong]
    exact forall_congr' fun i ↦ ih i v xs

/-- Recoding an encodable-carrier formula into `L_{ω₁ω}` preserves realization. -/
@[simp]
theorem realize_toOmega [Encodable ι] (φ : L.BoundedFormulaInf ι α n) (v : α → M)
    (xs : Fin n → M) : (toOmega φ).Realize v xs ↔ φ.Realize v xs :=
  realize_reindex _ φ v xs

end BoundedFormulaInf

namespace BoundedFormula

/-- The finitary embedding preserves realization, at every carrier. -/
@[simp]
theorem realize_toInf {M : Type w} [L.Structure M] :
    ∀ {n} (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M),
      (toInf (ι := ι) φ).Realize v xs ↔ φ.Realize v xs := by
  intro n φ
  induction φ with
  | falsum => intro v xs; exact Iff.rfl
  | equal t₁ t₂ => intro v xs; exact Iff.rfl
  | rel R ts => intro v xs; exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    intro v xs
    simp only [toInf, BoundedFormulaInf.realize_imp, BoundedFormula.realize_imp]
    exact imp_congr (ihφ v xs) (ihψ v xs)
  | all φ ih =>
    intro v xs
    simp only [toInf, BoundedFormulaInf.realize_all, BoundedFormula.realize_all]
    exact forall_congr' fun y ↦ ih v (Fin.snoc xs y)

end BoundedFormula

/-- Realization of an `L_{∞ω}` formula (no free bound variables). -/
def FormulaInf.Realize {M : Type w} [L.Structure M] (φ : L.FormulaInf ι α) (v : α → M) : Prop :=
  BoundedFormulaInf.Realize φ v default

section AllsExs

variable {M : Type w} [L.Structure M]

@[simp]
theorem BoundedFormulaInf.realize_alls {φ : L.BoundedFormulaInf ι α n} {v : α → M} :
    φ.alls.Realize v ↔ ∀ xs : Fin n → M, φ.Realize v xs := by
  induction n with
  | zero => exact Unique.forall_iff.symm
  | succ n ih =>
    simp only [BoundedFormulaInf.alls, ih, BoundedFormulaInf.realize_all]
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩

@[simp]
theorem BoundedFormulaInf.realize_exs {φ : L.BoundedFormulaInf ι α n} {v : α → M} :
    φ.exs.Realize v ↔ ∃ xs : Fin n → M, φ.Realize v xs := by
  induction n with
  | zero => exact Unique.exists_iff.symm
  | succ n ih =>
    simp only [BoundedFormulaInf.exs, ih, BoundedFormulaInf.realize_ex]
    constructor
    · rintro ⟨xs, x, h⟩
      exact ⟨_, h⟩
    · rintro ⟨xs, h⟩
      exact ⟨Fin.init xs, xs (Fin.last n), by rwa [Fin.snoc_init_self]⟩

end AllsExs

/-- Realization of an `L_{∞ω}` sentence in a structure. -/
def SentenceInf.Realize (φ : L.SentenceInf ι) (M : Type w) [L.Structure M] : Prop :=
  FormulaInf.Realize (M := M) φ Empty.elim

end Language

end FirstOrder
