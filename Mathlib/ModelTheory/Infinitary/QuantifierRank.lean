/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.ModelTheory.Infinitary.Syntax
public import Mathlib.SetTheory.Ordinal.Family

/-!
# Quantifier rank of infinitary formulas

The quantifier rank of an `L_{∞ω}` formula is an ordinal: quantifiers add a successor,
infinitary connectives take the supremum of their conjuncts' ranks. Because the branching
carrier `ι` is a type parameter, the rank is valued in `Ordinal.{uι}` — in particular, ranks of
`L_{ω₁ω}` formulas land in `Ordinal.{0}`, where Scott analysis needs them.

## Main statements

- `qrank_reindex`: carrier transport preserves quantifier rank up to `Ordinal.lift`. The
  `⊤`/`⊥` padding of the coded connectives contributes only rank-`0` branches, so the supremum
  is unchanged — including over empty carriers.
-/

@[expose] public section

universe u v u' uι uκ

namespace FirstOrder

namespace Language

namespace BoundedFormulaInf

variable {L : Language.{u, v}} {ι : Type uι} {κ : Type uκ} {α : Type u'} {n : ℕ}

/-- The quantifier rank of an infinitary formula, valued in the carrier's ordinal universe. -/
noncomputable def qrank : ∀ {n}, L.BoundedFormulaInf ι α n → Ordinal.{uι}
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (qrank φ) (qrank ψ)
  | _, .all φ => Order.succ (qrank φ)
  | _, .iSup φs => ⨆ i, qrank (φs i)
  | _, .iInf φs => ⨆ i, qrank (φs i)

@[simp]
theorem qrank_falsum : (falsum : L.BoundedFormulaInf ι α n).qrank = 0 :=
  rfl

@[simp]
theorem qrank_equal {t₁ t₂ : L.Term (α ⊕ Fin n)} :
    (equal t₁ t₂ : L.BoundedFormulaInf ι α n).qrank = 0 :=
  rfl

@[simp]
theorem qrank_rel {l : ℕ} {R : L.Relations l} {ts : Fin l → L.Term (α ⊕ Fin n)} :
    (rel R ts : L.BoundedFormulaInf ι α n).qrank = 0 :=
  rfl

@[simp]
theorem qrank_imp {φ ψ : L.BoundedFormulaInf ι α n} :
    (φ.imp ψ).qrank = max φ.qrank ψ.qrank :=
  rfl

@[simp]
theorem qrank_all {φ : L.BoundedFormulaInf ι α (n + 1)} :
    φ.all.qrank = Order.succ φ.qrank :=
  rfl

@[simp]
theorem qrank_iSup {φs : ι → L.BoundedFormulaInf ι α n} :
    (iSup φs).qrank = ⨆ i, (φs i).qrank :=
  rfl

@[simp]
theorem qrank_iInf {φs : ι → L.BoundedFormulaInf ι α n} :
    (iInf φs).qrank = ⨆ i, (φs i).qrank :=
  rfl

@[simp]
theorem qrank_top : (⊤ : L.BoundedFormulaInf ι α n).qrank = 0 :=
  max_self 0

@[simp]
theorem qrank_bot : (⊥ : L.BoundedFormulaInf ι α n).qrank = 0 :=
  rfl

/-- `Ordinal.lift` commutes with small suprema (including over empty index types). -/
private theorem lift_iSup_ord {ι' : Type uι} (f : ι' → Ordinal.{uι}) :
    Ordinal.lift.{uκ} (⨆ i, f i) = ⨆ i, Ordinal.lift.{uκ} (f i) := by
  haveI : Small.{max uι uκ} ι' := small_max.{uκ} ι'
  apply le_antisymm
  · have hub : (⨆ i, Ordinal.lift.{uκ} (f i)) ≤ Ordinal.lift.{uκ} (⨆ i, f i) :=
      Ordinal.iSup_le fun i ↦ Ordinal.lift_le.mpr (Ordinal.le_iSup f i)
    obtain ⟨t, ht⟩ := Ordinal.mem_range_lift_of_le hub
    rw [← ht]
    refine Ordinal.lift_le.mpr (Ordinal.iSup_le fun i ↦ Ordinal.lift_le.mp ?_)
    rw [ht]
    exact Ordinal.le_iSup (fun i ↦ Ordinal.lift.{uκ} (f i)) i
  · exact Ordinal.iSup_le fun i ↦ Ordinal.lift_le.mpr (Ordinal.le_iSup f i)

/-- Carrier transport preserves quantifier rank, up to `Ordinal.lift` between the two
carriers' ordinal universes. The padding of the coded connectives contributes only rank-`0`
branches, so the supremum survives — including over empty carriers, where both sides are
`0`. -/
theorem qrank_reindex (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n),
      Ordinal.lift.{uι} (reindex c φ).qrank = Ordinal.lift.{uκ} φ.qrank := by
  intro n φ
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ =>
    simp only [reindex_imp, qrank_imp]
    rw [Monotone.map_max fun _ _ h ↦ Ordinal.lift_le.mpr h,
      Monotone.map_max fun _ _ h ↦ Ordinal.lift_le.mpr h, ihφ, ihψ]
  | all φ ih =>
    simp only [reindex_all, qrank_all]
    rw [Ordinal.lift_succ, Ordinal.lift_succ, ih]
  | iSup φs ih =>
    haveI : Small.{max uι uκ} ι := small_max.{uκ} ι
    haveI : Small.{max uι uκ} κ := small_max.{uι} κ
    simp only [reindex_iSup, iSupAlong, qrank_iSup]
    rw [lift_iSup_ord, lift_iSup_ord]
    apply le_antisymm
    · refine Ordinal.iSup_le fun k ↦ ?_
      rcases hd : c.decode k with _ | i
      · rw [c.pad_of_decode_none hd, qrank_bot, Ordinal.lift_zero]
        exact Ordinal.bot_eq_zero ▸ bot_le
      · rw [c.pad_of_decode_some hd, ih i]
        exact Ordinal.le_iSup (fun i ↦ Ordinal.lift.{uκ} (φs i).qrank) i
    · refine Ordinal.iSup_le fun i ↦ ?_
      rw [← ih i]
      have hb := Ordinal.le_iSup
        (fun k ↦ Ordinal.lift.{uι} ((c.pad ⊥ fun i ↦ reindex c (φs i)) k).qrank) (c.encode i)
      rwa [IndexCoding.pad_encode] at hb
  | iInf φs ih =>
    haveI : Small.{max uι uκ} ι := small_max.{uκ} ι
    haveI : Small.{max uι uκ} κ := small_max.{uι} κ
    simp only [reindex_iInf, iInfAlong, qrank_iInf]
    rw [lift_iSup_ord, lift_iSup_ord]
    apply le_antisymm
    · refine Ordinal.iSup_le fun k ↦ ?_
      rcases hd : c.decode k with _ | i
      · rw [c.pad_of_decode_none hd, qrank_top, Ordinal.lift_zero]
        exact Ordinal.bot_eq_zero ▸ bot_le
      · rw [c.pad_of_decode_some hd, ih i]
        exact Ordinal.le_iSup (fun i ↦ Ordinal.lift.{uκ} (φs i).qrank) i
    · refine Ordinal.iSup_le fun i ↦ ?_
      rw [← ih i]
      have hb := Ordinal.le_iSup
        (fun k ↦ Ordinal.lift.{uι} ((c.pad ⊤ fun i ↦ reindex c (φs i)) k).qrank) (c.encode i)
      rwa [IndexCoding.pad_encode] at hb

/-- The recoding into `L_{ω₁ω}` preserves quantifier rank up to lift; since the target rank
lives in `Ordinal.{0}`, its lift into the source universe is the whole content. -/
theorem qrank_toOmega [Encodable ι] (φ : L.BoundedFormulaInf ι α n) :
    Ordinal.lift.{uι} (toOmega φ).qrank = Ordinal.lift.{0} φ.qrank :=
  qrank_reindex _ φ

end BoundedFormulaInf

end Language

end FirstOrder
