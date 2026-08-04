/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Logic.Encodable.Basic

/-!
# Index codings

An `IndexCoding ι κ` is an injection of `ι` into `κ` together with an explicit partial inverse.
Infinitary formulas (`FirstOrder.Language.BoundedFormulaInf`) fix one branching carrier per
formula; codings are how an `ι`-indexed infinitary connective is expressed at a larger carrier
`κ`, and how whole formulas are transported between carriers (`reindex`).

The `pad` operation extends an `ι`-indexed family to a `κ`-indexed one, sending indices that do
not decode to a given default value. For conjunctions the default is `⊤`, for disjunctions `⊥`,
which makes the padding semantically neutral.

## Main definitions

- `IndexCoding`: an encode/decode pair with `decode_encode`.
- `IndexCoding.id`, `IndexCoding.comp`: identity and composition.
- `IndexCoding.sumInl`, `IndexCoding.sumInr`: the canonical codings into a sum. These are what
  Karp's theorem uses: at the carrier `M ⊕ N`, both `M`-indexed and `N`-indexed conjunctions are
  available in a single formula type.
- `IndexCoding.ofEncodable`: the coding of an encodable type into `ℕ`, which recovers `L_{ω₁ω}`
  from a countable-carrier `L_{∞ω}` formula. This is deliberately stated for `Encodable`, not
  `Countable`: the coding itself involves no choice.
- `IndexCoding.ofEquiv`: the coding induced by an equivalence of carriers, whose `decode` is
  total. Reindexing along it is genuine syntactic transport (e.g. `ULift` universe
  adjustment), with a syntactic round trip.
- `IndexCoding.pad`: total extension of a family along a coding.
-/

@[expose] public section

universe uι uκ uμ

namespace FirstOrder

variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ}

/-- A coding of the index type `ι` into `κ`: an injection with an explicit partial inverse. -/
structure IndexCoding (ι : Type uι) (κ : Type uκ) where
  /-- The injection. -/
  encode : ι → κ
  /-- The partial inverse. -/
  decode : κ → Option ι
  /-- Decoding recovers every encoded index. -/
  decode_encode : ∀ i, decode (encode i) = some i

namespace IndexCoding

/-- Two codings with the same `encode` and `decode` are equal; the coherence proof is
irrelevant. -/
@[ext]
theorem ext {c₁ c₂ : IndexCoding ι κ} (he : c₁.encode = c₂.encode)
    (hd : c₁.decode = c₂.decode) : c₁ = c₂ := by
  cases c₁
  cases c₂
  cases he
  cases hd
  rfl

/-- The identity coding. -/
protected def id (ι : Type uι) : IndexCoding ι ι :=
  ⟨fun i ↦ i, some, fun _ ↦ rfl⟩

/-- Composition of codings. -/
def comp (c₂ : IndexCoding κ μ) (c₁ : IndexCoding ι κ) : IndexCoding ι μ where
  encode := c₂.encode ∘ c₁.encode
  decode m := (c₂.decode m).bind c₁.decode
  decode_encode i := by simp [Function.comp, c₂.decode_encode, c₁.decode_encode]

/-- The canonical coding of the left summand into a sum. -/
def sumInl (ι : Type uι) (κ : Type uκ) : IndexCoding ι (ι ⊕ κ) :=
  ⟨Sum.inl, Sum.getLeft?, fun _ ↦ rfl⟩

/-- The canonical coding of the right summand into a sum. -/
def sumInr (ι : Type uι) (κ : Type uκ) : IndexCoding κ (ι ⊕ κ) :=
  ⟨Sum.inr, Sum.getRight?, fun _ ↦ rfl⟩

/-- The canonical coding of an encodable type into `ℕ`. No choice is involved; a `Countable`
carrier can be upgraded noncomputably via `Encodable.ofCountable` at the call site. -/
def ofEncodable (ι : Type uι) [Encodable ι] : IndexCoding ι ℕ :=
  ⟨Encodable.encode, Encodable.decode, Encodable.encodek⟩

/-- The coding induced by an equivalence of carriers. Its `decode` is total, so reindexing
along it introduces no padding: this is the case of genuine syntactic transport (in
particular the `ULift` universe adjustment), as opposed to an arbitrary coding, which
preserves semantics but pads. -/
def ofEquiv (e : ι ≃ κ) : IndexCoding ι κ :=
  ⟨e, fun k ↦ some (e.symm k), fun i ↦ by simp⟩

/-- The two codings of an equivalence compose to the identity coding. -/
@[simp]
theorem ofEquiv_symm_comp (e : ι ≃ κ) :
    (ofEquiv e.symm).comp (ofEquiv e) = IndexCoding.id ι := by
  refine ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;>
    simp [comp, ofEquiv, IndexCoding.id]

/-- Total extension of a family along a coding: decoded indices select a branch, undecodable
ones get the default. -/
def pad {β : Sort*} (c : IndexCoding ι κ) (default : β) (f : ι → β) : κ → β :=
  fun k ↦ (c.decode k).elim default f

@[simp]
theorem pad_encode {β : Sort*} (c : IndexCoding ι κ) (default : β) (f : ι → β) (i : ι) :
    c.pad default f (c.encode i) = f i := by
  rw [pad, c.decode_encode]; rfl

theorem pad_of_decode_none {β : Sort*} (c : IndexCoding ι κ) {default : β} {f : ι → β} {k : κ}
    (h : c.decode k = none) : c.pad default f k = default := by
  rw [pad, h]; rfl

theorem pad_of_decode_some {β : Sort*} (c : IndexCoding ι κ) {default : β} {f : ι → β} {k : κ}
    {i : ι} (h : c.decode k = some i) : c.pad default f k = f i := by
  rw [pad, h]; rfl

@[simp]
theorem id_pad {β : Sort*} (default : β) (f : ι → β) : (IndexCoding.id ι).pad default f = f :=
  rfl

end IndexCoding

end FirstOrder
