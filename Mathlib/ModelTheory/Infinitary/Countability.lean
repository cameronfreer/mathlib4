/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.ModelTheory.Infinitary.Semantics
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Countability predicates for infinitary formulas

Formula-level cardinality bounds for `L_{∞ω}` formulas over a fixed carrier `ι`. A fixed
carrier does not mean every formula contains an infinitary node: a finitary formula at an
uncountable carrier is still countable. So these predicates remain *formula-sensitive* — they
demand a bound on `ι` only at the `iSup`/`iInf` nodes a formula actually contains.

## Main definitions

- `BoundedFormulaInf.IsCountable`: membership in `L_{ω₁ω}` — every infinitary node the formula
  contains has a countable carrier. Trivially true for infinitary-node-free formulas at any
  carrier, and true for all formulas under `[Countable ι]`.
- `BoundedFormulaInf.IsKappa`: membership in `L_{κω}`.
- `BoundedFormulaInf.indexBound`: the supremum of carrier cardinalities over the infinitary
  nodes actually present — `0` for a formula with no infinitary node, and `Cardinal.mk ι` once
  one occurs (`indexBound_iSup`, `indexBound_iInf`); always at most `Cardinal.mk ι`
  (`indexBound_le_mk`).
- `BoundedFormulaInf.ofCountable`: the proof-directed conversion to `L_{ω₁ω}`, recursing on
  the formula and extracting `Countable ι` from the proof only when it actually reaches an
  infinitary node. This is the formula-sensitive companion of the uniform `toOmega`
  (which requires `[Encodable ι]` for the whole carrier): in particular it converts finitary
  formulas at uncountable carriers, where no `Encodable ι` exists.
-/

universe u v u' uι w

namespace FirstOrder

namespace Language

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {n : ℕ}

@[expose] public section

/-- A formula is countable if every infinitary node it contains has a countable carrier.
This characterizes membership in `L_{ω₁ω}`; it is formula-sensitive — a formula with no
`iSup`/`iInf` node is countable at any carrier. -/
inductive IsCountable : ∀ {n}, L.BoundedFormulaInf ι α n → Prop
  /-- The false formula is countable. -/
  | falsum {n} : IsCountable (falsum (n := n))
  /-- Equalities are countable. -/
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : IsCountable (equal t₁ t₂)
  /-- Relation applications are countable. -/
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      IsCountable (rel R ts)
  /-- Implications of countable formulas are countable. -/
  | imp {n} {φ ψ : L.BoundedFormulaInf ι α n} :
      IsCountable φ → IsCountable ψ → IsCountable (φ.imp ψ)
  /-- Universal quantifications of countable formulas are countable. -/
  | all {n} {φ : L.BoundedFormulaInf ι α (n + 1)} : IsCountable φ → IsCountable φ.all
  /-- An infinitary disjunction is countable when the carrier is countable and every disjunct
  is. -/
  | iSup {n} {φs : ι → L.BoundedFormulaInf ι α n} :
      Countable ι → (∀ i, IsCountable (φs i)) → IsCountable (iSup φs)
  /-- An infinitary conjunction is countable when the carrier is countable and every conjunct
  is. -/
  | iInf {n} {φs : ι → L.BoundedFormulaInf ι α n} :
      Countable ι → (∀ i, IsCountable (φs i)) → IsCountable (iInf φs)

/-- Under a countable carrier, every formula is countable. -/
theorem isCountable_of_countable [Countable ι] :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n), φ.IsCountable := by
  intro n φ
  induction φ with
  | falsum => exact .falsum
  | equal t₁ t₂ => exact .equal t₁ t₂
  | rel R ts => exact .rel R ts
  | imp φ ψ ihφ ihψ => exact .imp ihφ ihψ
  | all φ ih => exact .all ih
  | iSup φs ih => exact .iSup ‹_› ih
  | iInf φs ih => exact .iInf ‹_› ih

/-- A formula has all its infinitary nodes' carriers of cardinality `< κ`.
This characterizes membership in `L_{κω}`; like `IsCountable`, it is formula-sensitive. -/
inductive IsKappa (κ : Cardinal.{uι}) : ∀ {n}, L.BoundedFormulaInf ι α n → Prop
  /-- The false formula is in every `L_{κω}`. -/
  | falsum {n} : IsKappa κ (falsum (n := n))
  /-- Equalities are in every `L_{κω}`. -/
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : IsKappa κ (equal t₁ t₂)
  /-- Relation applications are in every `L_{κω}`. -/
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      IsKappa κ (rel R ts)
  /-- Implication preserves `L_{κω}` membership. -/
  | imp {n} {φ ψ : L.BoundedFormulaInf ι α n} :
      IsKappa κ φ → IsKappa κ ψ → IsKappa κ (φ.imp ψ)
  /-- Universal quantification preserves `L_{κω}` membership. -/
  | all {n} {φ : L.BoundedFormulaInf ι α (n + 1)} : IsKappa κ φ → IsKappa κ φ.all
  /-- An infinitary disjunction is in `L_{κω}` when the carrier has cardinality `< κ` and
  every disjunct is. -/
  | iSup {n} {φs : ι → L.BoundedFormulaInf ι α n} :
      Cardinal.mk ι < κ → (∀ i, IsKappa κ (φs i)) → IsKappa κ (iSup φs)
  /-- An infinitary conjunction is in `L_{κω}` when the carrier has cardinality `< κ` and
  every conjunct is. -/
  | iInf {n} {φs : ι → L.BoundedFormulaInf ι α n} :
      Cardinal.mk ι < κ → (∀ i, IsKappa κ (φs i)) → IsKappa κ (iInf φs)

/-- `IsKappa` is monotone in the cardinal bound. -/
theorem IsKappa.mono {κ κ' : Cardinal.{uι}} (hle : κ ≤ κ') {φ : L.BoundedFormulaInf ι α n}
    (h : IsKappa κ φ) : IsKappa κ' φ := by
  induction h with
  | falsum => exact .falsum
  | equal t₁ t₂ => exact .equal t₁ t₂
  | rel R ts => exact .rel R ts
  | imp _ _ ih₁ ih₂ => exact .imp ih₁ ih₂
  | all _ ih => exact .all ih
  | iSup hcard _ ih => exact .iSup (hcard.trans_le hle) ih
  | iInf hcard _ ih => exact .iInf (hcard.trans_le hle) ih

/-- `IsCountable` is `IsKappa ℵ₁`. -/
theorem isCountable_iff_isKappa_aleph1 {φ : L.BoundedFormulaInf ι α n} :
    IsCountable φ ↔ IsKappa (Cardinal.aleph 1) φ := by
  constructor
  · intro h
    induction h with
    | falsum => exact .falsum
    | equal t₁ t₂ => exact .equal t₁ t₂
    | rel R ts => exact .rel R ts
    | imp _ _ ih₁ ih₂ => exact .imp ih₁ ih₂
    | all _ ih => exact .all ih
    | iSup hc _ ih => exact .iSup (Cardinal.mk_le_aleph0.trans_lt Cardinal.aleph0_lt_aleph_one) ih
    | iInf hc _ ih => exact .iInf (Cardinal.mk_le_aleph0.trans_lt Cardinal.aleph0_lt_aleph_one) ih
  · intro h
    induction h with
    | falsum => exact .falsum
    | equal t₁ t₂ => exact .equal t₁ t₂
    | rel R ts => exact .rel R ts
    | imp _ _ ih₁ ih₂ => exact .imp ih₁ ih₂
    | all _ ih => exact .all ih
    | iSup hcard _ ih =>
      have : Countable ι := by
        rw [← Cardinal.succ_aleph0] at hcard
        exact Cardinal.mk_le_aleph0_iff.mp (Order.lt_succ_iff.mp hcard)
      exact .iSup this ih
    | iInf hcard _ ih =>
      have : Countable ι := by
        rw [← Cardinal.succ_aleph0] at hcard
        exact Cardinal.mk_le_aleph0_iff.mp (Order.lt_succ_iff.mp hcard)
      exact .iInf this ih

/-! ### The index bound -/

/-- The supremum of carrier cardinalities over the infinitary nodes a formula actually
contains: `0` for a formula with no infinitary node, `Cardinal.mk ι` once one occurs. -/
noncomputable def indexBound : ∀ {n}, L.BoundedFormulaInf ι α n → Cardinal.{uι}
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (indexBound φ) (indexBound ψ)
  | _, .all φ => indexBound φ
  | _, .iSup φs => max (Cardinal.mk ι) (⨆ i, indexBound (φs i))
  | _, .iInf φs => max (Cardinal.mk ι) (⨆ i, indexBound (φs i))

@[simp]
theorem indexBound_falsum : (falsum : L.BoundedFormulaInf ι α n).indexBound = 0 :=
  rfl

@[simp]
theorem indexBound_equal {t₁ t₂ : L.Term (α ⊕ Fin n)} :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).indexBound = 0 :=
  rfl

@[simp]
theorem indexBound_rel {l : ℕ} {R : L.Relations l} {ts : Fin l → L.Term (α ⊕ Fin n)} :
    (rel R ts : L.BoundedFormulaInf ι α n).indexBound = 0 :=
  rfl

@[simp]
theorem indexBound_imp {φ ψ : L.BoundedFormulaInf ι α n} :
    (φ.imp ψ).indexBound = max φ.indexBound ψ.indexBound :=
  rfl

@[simp]
theorem indexBound_all {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.all.indexBound = φ.indexBound :=
  rfl

/-- The index bound never exceeds the carrier's cardinality. -/
theorem indexBound_le_mk : ∀ {n} (φ : L.BoundedFormulaInf ι α n),
    φ.indexBound ≤ Cardinal.mk ι := by
  intro n φ
  induction φ with
  | falsum => exact zero_le _
  | equal t₁ t₂ => exact zero_le _
  | rel R ts => exact zero_le _
  | imp φ ψ ihφ ihψ => exact max_le ihφ ihψ
  | all φ ih => exact ih
  | iSup φs ih => exact max_le le_rfl (ciSup_le' fun i ↦ ih i)
  | iInf φs ih => exact max_le le_rfl (ciSup_le' fun i ↦ ih i)

/-- At an infinitary disjunction, the index bound is exactly the carrier's cardinality: the
children's bounds are absorbed by `indexBound_le_mk`. -/
@[simp]
theorem indexBound_iSup {φs : ι → L.BoundedFormulaInf ι α n} :
    (iSup φs).indexBound = Cardinal.mk ι :=
  max_eq_left (ciSup_le' fun i ↦ indexBound_le_mk (φs i))

/-- At an infinitary conjunction, the index bound is exactly the carrier's cardinality. -/
@[simp]
theorem indexBound_iInf {φs : ι → L.BoundedFormulaInf ι α n} :
    (iInf φs).indexBound = Cardinal.mk ι :=
  max_eq_left (ciSup_le' fun i ↦ indexBound_le_mk (φs i))

/-- Every formula belongs to `L_{κω}` for `κ` the successor of its index bound. -/
theorem isKappa_succ_indexBound (φ : L.BoundedFormulaInf ι α n) :
    IsKappa (Order.succ φ.indexBound) φ := by
  induction φ with
  | falsum => exact .falsum
  | equal t₁ t₂ => exact .equal t₁ t₂
  | rel R ts => exact .rel R ts
  | imp φ ψ ih₁ ih₂ =>
    exact .imp (ih₁.mono (Order.succ_le_succ (le_max_left _ _)))
      (ih₂.mono (Order.succ_le_succ (le_max_right _ _)))
  | all φ ih => exact .all ih
  | iSup φs ih =>
    refine .iSup (Order.lt_succ_of_le (by simp)) fun i ↦ (ih i).mono ?_
    exact Order.succ_le_succ ((indexBound_le_mk (φs i)).trans (by simp))
  | iInf φs ih =>
    refine .iInf (Order.lt_succ_of_le (by simp)) fun i ↦ (ih i).mono ?_
    exact Order.succ_le_succ ((indexBound_le_mk (φs i)).trans (by simp))

/-- Every `L_{∞ω}` formula belongs to some `L_{κω}`. -/
theorem exists_isKappa (φ : L.BoundedFormulaInf ι α n) : ∃ κ : Cardinal.{uι}, IsKappa κ φ :=
  ⟨Order.succ φ.indexBound, isKappa_succ_indexBound φ⟩

/-! ### The proof-directed conversion to `L_{ω₁ω}` -/

namespace IsCountable

theorem imp_left {φ ψ : L.BoundedFormulaInf ι α n} (h : (φ.imp ψ).IsCountable) :
    φ.IsCountable := by
  cases h with
  | imp hφ _ => exact hφ

theorem imp_right {φ ψ : L.BoundedFormulaInf ι α n} (h : (φ.imp ψ).IsCountable) :
    ψ.IsCountable := by
  cases h with
  | imp _ hψ => exact hψ

theorem all_inner {φ : L.BoundedFormulaInf ι α (n + 1)} (h : φ.all.IsCountable) :
    φ.IsCountable := by
  cases h with
  | all hφ => exact hφ

theorem iSup_countable {φs : ι → L.BoundedFormulaInf ι α n}
    (h : (BoundedFormulaInf.iSup φs).IsCountable) : Countable ι := by
  cases h with
  | iSup hc _ => exact hc

theorem iSup_forall {φs : ι → L.BoundedFormulaInf ι α n}
    (h : (BoundedFormulaInf.iSup φs).IsCountable) : ∀ i, (φs i).IsCountable := by
  cases h with
  | iSup _ hφs => exact hφs

theorem iInf_countable {φs : ι → L.BoundedFormulaInf ι α n}
    (h : (BoundedFormulaInf.iInf φs).IsCountable) : Countable ι := by
  cases h with
  | iInf hc _ => exact hc

theorem iInf_forall {φs : ι → L.BoundedFormulaInf ι α n}
    (h : (BoundedFormulaInf.iInf φs).IsCountable) : ∀ i, (φs i).IsCountable := by
  cases h with
  | iInf _ hφs => exact hφs

end IsCountable

/-- The proof-directed conversion of a countable formula to `L_{ω₁ω}`. Recurses on the
formula, extracting `Countable ι` from the proof — and hence choosing an encoding — only when
it actually reaches an infinitary node. In particular it converts formulas with no infinitary
node at arbitrary, possibly uncountable, carriers, where `toOmega` is unavailable. -/
noncomputable def ofCountable :
    ∀ {n} {φ : L.BoundedFormulaInf ι α n}, φ.IsCountable → L.BoundedFormulaω α n
  | _, .falsum, _ => .falsum
  | _, .equal t₁ t₂, _ => .equal t₁ t₂
  | _, .rel R ts, _ => .rel R ts
  | _, .imp _ _, h => (ofCountable h.imp_left).imp (ofCountable h.imp_right)
  | _, .all _, h => (ofCountable h.all_inner).all
  | _, .iSup _, h =>
    haveI : Countable ι := h.iSup_countable
    haveI : Encodable ι := Encodable.ofCountable ι
    iSupAlong (.ofEncodable ι) fun i ↦ ofCountable (h.iSup_forall i)
  | _, .iInf _, h =>
    haveI : Countable ι := h.iInf_countable
    haveI : Encodable ι := Encodable.ofCountable ι
    iInfAlong (.ofEncodable ι) fun i ↦ ofCountable (h.iInf_forall i)

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

/-- The proof-directed conversion preserves realization. -/
@[simp]
theorem realize_ofCountable {φ : L.BoundedFormulaInf ι α n} (h : φ.IsCountable) :
    (ofCountable h).Realize v xs ↔ φ.Realize v xs := by
  induction h with
  | falsum => exact Iff.rfl
  | equal t₁ t₂ => exact Iff.rfl
  | rel R ts => exact Iff.rfl
  | imp _ _ ih₁ ih₂ => simp only [ofCountable, realize_imp, ih₁, ih₂]
  | all _ ih =>
    simp only [ofCountable, realize_all]
    exact forall_congr' fun x ↦ ih
  | iSup _ _ ih =>
    simp only [ofCountable, realize_iSupAlong, realize_iSup]
    exact exists_congr fun i ↦ ih i
  | iInf _ _ ih =>
    simp only [ofCountable, realize_iInfAlong, realize_iInf]
    exact forall_congr' fun i ↦ ih i

/-- Encoding independence: different `IsCountable` proofs may choose different encodings and
so produce syntactically different `L_{ω₁ω}` formulas, but their realizations agree. -/
theorem realize_ofCountable_congr {φ : L.BoundedFormulaInf ι α n}
    (h₁ h₂ : φ.IsCountable) :
    (ofCountable h₁).Realize v xs ↔ (ofCountable h₂).Realize v xs :=
  (realize_ofCountable h₁).trans (realize_ofCountable h₂).symm

end

end BoundedFormulaInf

namespace BoundedFormula

@[expose] public section

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {n : ℕ}

/-- The finitary embedding is countable at EVERY carrier, with no countability assumption:
`toInf` produces no infinitary node, so formula-sensitivity is exactly what makes this true at
an uncountable carrier. -/
theorem isCountable_toInf : ∀ {n} (φ : L.BoundedFormula α n),
    (toInf (ι := ι) φ).IsCountable := by
  intro n φ
  induction φ with
  | falsum => exact .falsum
  | equal t₁ t₂ => exact .equal t₁ t₂
  | rel R ts => exact .rel R ts
  | imp φ ψ ihφ ihψ => exact .imp ihφ ihψ
  | all φ ih => exact .all ih

/-- The finitary embedding has index bound `0` at every carrier: the bound measures the
infinitary nodes actually present, not the ambient carrier. -/
@[simp]
theorem indexBound_toInf : ∀ {n} (φ : L.BoundedFormula α n),
    (toInf (ι := ι) φ).indexBound = 0 := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => simp only [toInf, BoundedFormulaInf.indexBound_imp, ihφ, ihψ, max_self]
  | all φ ih => exact ih

end

end BoundedFormula

end Language

end FirstOrder
