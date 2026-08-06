/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.ModelTheory.Infinitary.Reindex

/-!
# Language maps on infinitary formulas

`LHom.onBoundedFormulaInf` applies a language homomorphism to an infinitary formula, leaving
the branching carrier untouched. The representative coherence law here is
`LHom.onBoundedFormulaInf_reindex`: ordinary formula transformations (which act at a fixed
carrier) commute with carrier transport (`reindex`). This is the expected long-term shape for
every syntax operation on the carrier-parameterized type.
-/

universe u v u₂ v₂ u' uι uκ

namespace FirstOrder

namespace Language

namespace LHom

@[expose] public section

open BoundedFormulaInf

variable {L : Language.{u, v}} {L' : Language.{u₂, v₂}} {ι : Type uι} {κ : Type uκ}
  {α : Type u'} {n : ℕ}

/-- Applies a language homomorphism to an infinitary formula, at the same carrier. -/
def onBoundedFormulaInf (g : L →ᴸ L') :
    ∀ {n}, L.BoundedFormulaInf ι α n → L'.BoundedFormulaInf ι α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (g.onTerm t₁) (g.onTerm t₂)
  | _, .rel R ts => .rel (g.onRelation R) fun i ↦ g.onTerm (ts i)
  | _, .imp φ ψ => (onBoundedFormulaInf g φ).imp (onBoundedFormulaInf g ψ)
  | _, .all φ => (onBoundedFormulaInf g φ).all
  | _, .iSup φs => .iSup fun i ↦ onBoundedFormulaInf g (φs i)
  | _, .iInf φs => .iInf fun i ↦ onBoundedFormulaInf g (φs i)

@[simp]
theorem onBoundedFormulaInf_top (g : L →ᴸ L') :
    g.onBoundedFormulaInf (⊤ : L.BoundedFormulaInf ι α n) = ⊤ :=
  rfl

@[simp]
theorem onBoundedFormulaInf_bot (g : L →ᴸ L') :
    g.onBoundedFormulaInf (⊥ : L.BoundedFormulaInf ι α n) = ⊥ :=
  rfl

/-- Language maps commute with carrier transport: transforming the formula at carrier `ι` and
then reindexing to `κ` is the same as reindexing first and transforming at `κ`. Proved from
the generic pad law `IndexCoding.comp_pad`, with no decoder analysis. -/
theorem onBoundedFormulaInf_reindex (g : L →ᴸ L') (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaInf ι α n),
      g.onBoundedFormulaInf (reindex c φ) = reindex c (g.onBoundedFormulaInf φ) := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ =>
    simp only [onBoundedFormulaInf, reindex_imp, ihφ, ihψ]
  | all φ ih =>
    simp only [onBoundedFormulaInf, reindex_all, ih]
  | iSup φs ih =>
    have h : (g.onBoundedFormulaInf ∘ c.pad ⊥ fun i ↦ reindex c (φs i)) =
        c.pad ⊥ fun i ↦ reindex c (g.onBoundedFormulaInf (φs i)) :=
      calc (g.onBoundedFormulaInf ∘ c.pad ⊥ fun i ↦ reindex c (φs i))
          = c.pad ⊥ (g.onBoundedFormulaInf ∘ fun i ↦ reindex c (φs i)) := by
            rw [IndexCoding.comp_pad, onBoundedFormulaInf_bot]
        _ = c.pad ⊥ fun i ↦ reindex c (g.onBoundedFormulaInf (φs i)) :=
            congrArg _ (funext fun i ↦ ih i)
    exact congrArg BoundedFormulaInf.iSup h
  | iInf φs ih =>
    have h : (g.onBoundedFormulaInf ∘ c.pad ⊤ fun i ↦ reindex c (φs i)) =
        c.pad ⊤ fun i ↦ reindex c (g.onBoundedFormulaInf (φs i)) :=
      calc (g.onBoundedFormulaInf ∘ c.pad ⊤ fun i ↦ reindex c (φs i))
          = c.pad ⊤ (g.onBoundedFormulaInf ∘ fun i ↦ reindex c (φs i)) := by
            rw [IndexCoding.comp_pad, onBoundedFormulaInf_top]
        _ = c.pad ⊤ fun i ↦ reindex c (g.onBoundedFormulaInf (φs i)) :=
            congrArg _ (funext fun i ↦ ih i)
    exact congrArg BoundedFormulaInf.iInf h

end

end LHom

end Language

end FirstOrder
