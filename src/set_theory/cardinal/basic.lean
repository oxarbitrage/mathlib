/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
import data.nat.enat
import data.set.countable
import logic.small
import order.conditionally_complete_lattice
import order.succ_pred.basic
import set_theory.cardinal.schroeder_bernstein

/-!
# Cardinal Numbers

We define cardinal numbers as a quotient of types under the equivalence relation of equinumerity.

## Main definitions

* `cardinal` the type of cardinal numbers (in a given universe).
* `cardinal.mk α` or `#α` is the cardinality of `α`. The notation `#` lives in the locale
  `cardinal`.
* There is an instance that `cardinal` forms a `canonically_ordered_comm_semiring`.
* Addition `c₁ + c₂` is defined by `cardinal.add_def α β : #α + #β = #(α ⊕ β)`.
* Multiplication `c₁ * c₂` is defined by `cardinal.mul_def : #α * #β = #(α × β)`.
* The order `c₁ ≤ c₂` is defined by `cardinal.le_def α β : #α ≤ #β ↔ nonempty (α ↪ β)`.
* Exponentiation `c₁ ^ c₂` is defined by `cardinal.power_def α β : #α ^ #β = #(β → α)`.
* `cardinal.aleph_0` or `ℵ₀` is the cardinality of `ℕ`. This definition is universe polymorphic:
  `cardinal.aleph_0.{u} : cardinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.
* `cardinal.min (I : nonempty ι) (c : ι → cardinal)` is the minimal cardinal in the range of `c`.
* `order.succ c` is the successor cardinal, the smallest cardinal larger than `c`.
* `cardinal.sum` is the sum of a collection of cardinals.
* `cardinal.sup` is the supremum of a collection of cardinals.
* `cardinal.powerlt c₁ c₂` or `c₁ ^< c₂` is defined as `sup_{γ < β} α^γ`.

## Main Statements

* Cantor's theorem: `cardinal.cantor c : c < 2 ^ c`.
* König's theorem: `cardinal.sum_lt_prod`

## Implementation notes

* There is a type of cardinal numbers in every universe level:
  `cardinal.{u} : Type (u + 1)` is the quotient of types in `Type u`.
  The operation `cardinal.lift` lifts cardinal numbers to a higher level.
* Cardinal arithmetic specifically for infinite cardinals (like `κ * κ = κ`) is in the file
  `set_theory/cardinal_ordinal.lean`.
* There is an instance `has_pow cardinal`, but this will only fire if Lean already knows that both
  the base and the exponent live in the same universe. As a workaround, you can add
  ```
    local infixr ^ := @has_pow.pow cardinal cardinal cardinal.has_pow
  ```
  to a file. This notation will work even if Lean doesn't know yet that the base and the exponent
  live in the same universe (but no exponents in other types can be used).

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/

open function set order
open_locale classical

noncomputable theory

universes u v w
variables {α β : Type u}

/-- The equivalence relation on types given by equivalence (bijective correspondence) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
-/
instance cardinal.is_equivalent : setoid (Type u) :=
{ r := λ α β, nonempty (α ≃ β),
  iseqv := ⟨λ α,
    ⟨equiv.refl α⟩,
    λ α β ⟨e⟩, ⟨e.symm⟩,
    λ α β γ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩⟩ }

/-- `cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
def cardinal : Type (u + 1) := quotient cardinal.is_equivalent

namespace cardinal

/-- The cardinal number of a type -/
def mk : Type u → cardinal := quotient.mk

localized "notation `#` := cardinal.mk" in cardinal

instance can_lift_cardinal_Type : can_lift cardinal.{u} (Type u) :=
⟨mk, λ c, true, λ c _, quot.induction_on c $ λ α, ⟨α, rfl⟩⟩

@[elab_as_eliminator]
lemma induction_on {p : cardinal → Prop} (c : cardinal) (h : ∀ α, p (#α)) : p c :=
quotient.induction_on c h

@[elab_as_eliminator]
lemma induction_on₂ {p : cardinal → cardinal → Prop} (c₁ : cardinal) (c₂ : cardinal)
  (h : ∀ α β, p (#α) (#β)) : p c₁ c₂ :=
quotient.induction_on₂ c₁ c₂ h

@[elab_as_eliminator]
lemma induction_on₃ {p : cardinal → cardinal → cardinal → Prop} (c₁ : cardinal) (c₂ : cardinal)
  (c₃ : cardinal) (h : ∀ α β γ, p (#α) (#β) (#γ)) : p c₁ c₂ c₃ :=
quotient.induction_on₃ c₁ c₂ c₃ h

protected lemma eq : #α = #β ↔ nonempty (α ≃ β) := quotient.eq

@[simp] theorem mk_def (α : Type u) : @eq cardinal ⟦α⟧ (#α) := rfl

@[simp] theorem mk_out (c : cardinal) : #(c.out) = c := quotient.out_eq _

/-- The representative of the cardinal of a type is equivalent ot the original type. -/
def out_mk_equiv {α : Type v} : (#α).out ≃ α :=
nonempty.some $ cardinal.eq.mp (by simp)

lemma mk_congr (e : α ≃ β) : # α = # β := quot.sound ⟨e⟩

alias mk_congr ← equiv.cardinal_eq

/-- Lift a function between `Type*`s to a function between `cardinal`s. -/
def map (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) :
  cardinal.{u} → cardinal.{v} :=
quotient.map f (λ α β ⟨e⟩, ⟨hf α β e⟩)

@[simp] lemma map_mk (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) (α : Type u) :
  map f hf (#α) = #(f α) := rfl

/-- Lift a binary operation `Type* → Type* → Type*` to a binary operation on `cardinal`s. -/
def map₂ (f : Type u → Type v → Type w) (hf : ∀ α β γ δ, α ≃ β → γ ≃ δ → f α γ ≃ f β δ) :
  cardinal.{u} → cardinal.{v} → cardinal.{w} :=
quotient.map₂ f $ λ α β ⟨e₁⟩ γ δ ⟨e₂⟩, ⟨hf α β γ δ e₁ e₂⟩

/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : cardinal.{v} → cardinal.{max v u}` -/
def lift (c : cardinal.{v}) : cardinal.{max v u} :=
map ulift (λ α β e, equiv.ulift.trans $ e.trans equiv.ulift.symm) c

@[simp] theorem mk_ulift (α) : #(ulift.{v u} α) = lift.{v} (#α) := rfl

theorem lift_umax : lift.{(max u v) u} = lift.{v u} :=
funext $ λ a, induction_on a $ λ α, (equiv.ulift.trans equiv.ulift.symm).cardinal_eq

theorem lift_umax' : lift.{(max v u) u} = lift.{v u} := lift_umax

theorem lift_id' (a : cardinal.{max u v}) : lift.{u} a = a :=
induction_on a $ λ α, mk_congr equiv.ulift

@[simp] theorem lift_id (a : cardinal) : lift.{u u} a = a := lift_id'.{u u} a
@[simp] theorem lift_uzero (a : cardinal.{u}) : lift.{0} a = a := lift_id'.{0 u} a

@[simp] theorem lift_lift (a : cardinal) :
  lift.{w} (lift.{v} a) = lift.{max v w} a :=
induction_on a $ λ α,
(equiv.ulift.trans $ equiv.ulift.trans equiv.ulift.symm).cardinal_eq

/-- We define the order on cardinal numbers by `#α ≤ #β` if and only if
  there exists an embedding (injective function) from α to β. -/
instance : has_le cardinal.{u} :=
⟨λ q₁ q₂, quotient.lift_on₂ q₁ q₂ (λ α β, nonempty $ α ↪ β) $
  λ α β γ δ ⟨e₁⟩ ⟨e₂⟩, propext ⟨λ ⟨e⟩, ⟨e.congr e₁ e₂⟩, λ ⟨e⟩, ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

instance : partial_order cardinal.{u} :=
{ le          := (≤),
  le_refl     := by rintros ⟨α⟩; exact ⟨embedding.refl _⟩,
  le_trans    := by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.trans e₂⟩,
  le_antisymm := by { rintros ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩, exact quotient.sound (e₁.antisymm e₂) } }

theorem le_def (α β : Type u) : #α ≤ #β ↔ nonempty (α ↪ β) :=
iff.rfl

theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : injective f) : #α ≤ #β :=
⟨⟨f, hf⟩⟩

theorem _root_.function.embedding.cardinal_le {α β : Type u} (f : α ↪ β) : #α ≤ #β := ⟨f⟩

theorem mk_le_of_surjective {α β : Type u} {f : α → β} (hf : surjective f) : #β ≤ #α :=
⟨embedding.of_surjective f hf⟩

theorem le_mk_iff_exists_set {c : cardinal} {α : Type u} :
  c ≤ #α ↔ ∃ p : set α, #p = c :=
⟨induction_on c $ λ β ⟨⟨f, hf⟩⟩,
  ⟨set.range f, (equiv.of_injective f hf).cardinal_eq.symm⟩,
λ ⟨p, e⟩, e ▸ ⟨⟨subtype.val, λ a b, subtype.eq⟩⟩⟩

theorem mk_subtype_le {α : Type u} (p : α → Prop) : #(subtype p) ≤ #α :=
⟨embedding.subtype p⟩

theorem mk_set_le (s : set α) : #s ≤ #α :=
mk_subtype_le s

theorem out_embedding {c c' : cardinal} : c ≤ c' ↔ nonempty (c.out ↪ c'.out) :=
by { transitivity _, rw [←quotient.out_eq c, ←quotient.out_eq c'], refl }

theorem lift_mk_le {α : Type u} {β : Type v} :
  lift.{(max v w)} (#α) ≤ lift.{max u w} (#β) ↔ nonempty (α ↪ β) :=
⟨λ ⟨f⟩, ⟨embedding.congr equiv.ulift equiv.ulift f⟩,
 λ ⟨f⟩, ⟨embedding.congr equiv.ulift.symm equiv.ulift.symm f⟩⟩

/-- A variant of `cardinal.lift_mk_le` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_le' {α : Type u} {β : Type v} :
  lift.{v} (#α) ≤ lift.{u} (#β) ↔ nonempty (α ↪ β) :=
lift_mk_le.{u v 0}

theorem lift_mk_eq {α : Type u} {β : Type v} :
  lift.{max v w} (#α) = lift.{max u w} (#β) ↔ nonempty (α ≃ β) :=
quotient.eq.trans
⟨λ ⟨f⟩, ⟨equiv.ulift.symm.trans $ f.trans equiv.ulift⟩,
 λ ⟨f⟩, ⟨equiv.ulift.trans $ f.trans equiv.ulift.symm⟩⟩

/-- A variant of `cardinal.lift_mk_eq` with specialized universes.
Because Lean often can not realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
theorem lift_mk_eq' {α : Type u} {β : Type v} :
  lift.{v} (#α) = lift.{u} (#β) ↔ nonempty (α ≃ β) :=
lift_mk_eq.{u v 0}

@[simp] theorem lift_le {a b : cardinal} : lift a ≤ lift b ↔ a ≤ b :=
induction_on₂ a b $ λ α β, by { rw ← lift_umax, exact lift_mk_le }

/-- `cardinal.lift` as an `order_embedding`. -/
@[simps { fully_applied := ff }] def lift_order_embedding : cardinal.{v} ↪o cardinal.{max v u} :=
order_embedding.of_map_le_iff lift (λ _ _, lift_le)

theorem lift_injective : injective lift.{u v} := lift_order_embedding.injective

@[simp] theorem lift_inj {a b : cardinal} : lift a = lift b ↔ a = b :=
lift_injective.eq_iff

@[simp] theorem lift_lt {a b : cardinal} : lift a < lift b ↔ a < b :=
lift_order_embedding.lt_iff_lt

theorem lift_strict_mono : strict_mono lift :=
λ a b, lift_lt.2

theorem lift_monotone : monotone lift :=
lift_strict_mono.monotone

instance : has_zero cardinal.{u} := ⟨#pempty⟩

instance : inhabited cardinal.{u} := ⟨0⟩

lemma mk_eq_zero (α : Type u) [is_empty α] : #α = 0 :=
(equiv.equiv_pempty α).cardinal_eq

@[simp] theorem lift_zero : lift 0 = 0 := mk_congr (equiv.equiv_pempty _)

@[simp] theorem lift_eq_zero {a : cardinal.{v}} : lift.{u} a = 0 ↔ a = 0 :=
lift_injective.eq_iff' lift_zero

lemma mk_eq_zero_iff {α : Type u} : #α = 0 ↔ is_empty α :=
⟨λ e, let ⟨h⟩ := quotient.exact e in h.is_empty, @mk_eq_zero α⟩

theorem mk_ne_zero_iff {α : Type u} : #α ≠ 0 ↔ nonempty α :=
(not_iff_not.2 mk_eq_zero_iff).trans not_is_empty_iff

@[simp] lemma mk_ne_zero (α : Type u) [nonempty α] : #α ≠ 0 := mk_ne_zero_iff.2 ‹_›

instance : has_one cardinal.{u} := ⟨#punit⟩

instance : nontrivial cardinal.{u} := ⟨⟨1, 0, mk_ne_zero _⟩⟩

lemma mk_eq_one (α : Type u) [unique α] : #α = 1 :=
(equiv.equiv_punit α).cardinal_eq

theorem le_one_iff_subsingleton {α : Type u} : #α ≤ 1 ↔ subsingleton α :=
⟨λ ⟨f⟩, ⟨λ a b, f.injective (subsingleton.elim _ _)⟩,
 λ ⟨h⟩, ⟨⟨λ a, punit.star, λ a b _, h _ _⟩⟩⟩

instance : has_add cardinal.{u} := ⟨map₂ sum $ λ α β γ δ, equiv.sum_congr⟩

theorem add_def (α β : Type u) : #α + #β = #(α ⊕ β) := rfl

@[simp] lemma mk_sum (α : Type u) (β : Type v) :
  #(α ⊕ β) = lift.{v u} (#α) + lift.{u v} (#β) :=
mk_congr ((equiv.ulift).symm.sum_congr (equiv.ulift).symm)

@[simp] theorem mk_option {α : Type u} : #(option α) = #α + 1 :=
(equiv.option_equiv_sum_punit α).cardinal_eq

@[simp] lemma mk_psum (α : Type u) (β : Type v) : #(psum α β) = lift.{v} (#α) + lift.{u} (#β) :=
(mk_congr (equiv.psum_equiv_sum α β)).trans (mk_sum α β)

@[simp] lemma mk_fintype (α : Type u) [fintype α] : #α = fintype.card α :=
begin
  refine fintype.induction_empty_option' _ _ _ α,
  { introsI α β h e hα, letI := fintype.of_equiv β e.symm,
    rwa [mk_congr e, fintype.card_congr e] at hα },
  { refl },
  { introsI α h hα, simp [hα] }
end

instance : has_mul cardinal.{u} := ⟨map₂ prod $ λ α β γ δ, equiv.prod_congr⟩

theorem mul_def (α β : Type u) : #α * #β = #(α × β) := rfl

@[simp] lemma mk_prod (α : Type u) (β : Type v) :
  #(α × β) = lift.{v u} (#α) * lift.{u v} (#β) :=
mk_congr (equiv.ulift.symm.prod_congr (equiv.ulift).symm)

private theorem mul_comm' (a b : cardinal.{u}) : a * b = b * a :=
induction_on₂ a b $ λ α β, mk_congr $ equiv.prod_comm α β

/-- The cardinal exponential. `#α ^ #β` is the cardinal of `β → α`. -/
instance : has_pow cardinal.{u} cardinal.{u} :=
⟨map₂ (λ α β, β → α) (λ α β γ δ e₁ e₂, e₂.arrow_congr e₁)⟩

local infixr ^ := @has_pow.pow cardinal cardinal cardinal.has_pow
local infixr ` ^ℕ `:80 := @has_pow.pow cardinal ℕ monoid.has_pow

theorem power_def (α β) : #α ^ #β = #(β → α) := rfl

theorem mk_arrow (α : Type u) (β : Type v) : #(α → β) = lift.{u} (#β) ^ lift.{v} (#α) :=
mk_congr (equiv.ulift.symm.arrow_congr equiv.ulift.symm)

@[simp] theorem lift_power (a b) : lift (a ^ b) = lift a ^ lift b :=
induction_on₂ a b $ λ α β,
mk_congr $ equiv.ulift.trans (equiv.ulift.arrow_congr equiv.ulift).symm

@[simp] theorem power_zero {a : cardinal} : a ^ 0 = 1 :=
induction_on a $ λ α, mk_congr $ equiv.pempty_arrow_equiv_punit α

@[simp] theorem power_one {a : cardinal} : a ^ 1 = a :=
induction_on a $ λ α, mk_congr $ equiv.punit_arrow_equiv α

theorem power_add {a b c : cardinal} : a ^ (b + c) = a ^ b * a ^ c :=
induction_on₃ a b c $ λ α β γ, mk_congr $ equiv.sum_arrow_equiv_prod_arrow β γ α

instance : comm_semiring cardinal.{u} :=
{ zero          := 0,
  one           := 1,
  add           := (+),
  mul           := (*),
  zero_add      := λ a, induction_on a $ λ α, mk_congr $ equiv.empty_sum pempty α,
  add_zero      := λ a, induction_on a $ λ α, mk_congr $ equiv.sum_empty α pempty,
  add_assoc     := λ a b c, induction_on₃ a b c $ λ α β γ, mk_congr $ equiv.sum_assoc α β γ,
  add_comm      := λ a b, induction_on₂ a b $ λ α β, mk_congr $ equiv.sum_comm α β,
  zero_mul      := λ a, induction_on a $ λ α, mk_congr $ equiv.pempty_prod α,
  mul_zero      := λ a, induction_on a $ λ α, mk_congr $ equiv.prod_pempty α,
  one_mul       := λ a, induction_on a $ λ α, mk_congr $ equiv.punit_prod α,
  mul_one       := λ a, induction_on a $ λ α, mk_congr $ equiv.prod_punit α,
  mul_assoc     := λ a b c, induction_on₃ a b c $ λ α β γ, mk_congr $ equiv.prod_assoc α β γ,
  mul_comm      := mul_comm',
  left_distrib  := λ a b c, induction_on₃ a b c $ λ α β γ, mk_congr $ equiv.prod_sum_distrib α β γ,
  right_distrib := λ a b c, induction_on₃ a b c $ λ α β γ, mk_congr $ equiv.sum_prod_distrib α β γ,
  npow          := λ n c, c ^ n,
  npow_zero'    := @power_zero,
  npow_succ'    := λ n c, by rw [nat.cast_succ, power_add, power_one, mul_comm'] }

theorem power_bit0 (a b : cardinal) : a ^ (bit0 b) = a ^ b * a ^ b :=
power_add

theorem power_bit1 (a b : cardinal) : a ^ (bit1 b) = a ^ b * a ^ b * a :=
by rw [bit1, ←power_bit0, power_add, power_one]

@[simp] theorem one_power {a : cardinal} : 1 ^ a = 1 :=
induction_on a $ λ α, (equiv.arrow_punit_equiv_punit α).cardinal_eq

@[simp] theorem mk_bool : #bool = 2 := by simp

@[simp] theorem mk_Prop : #(Prop) = 2 := by simp

@[simp] theorem zero_power {a : cardinal} : a ≠ 0 → 0 ^ a = 0 :=
induction_on a $ λ α heq, mk_eq_zero_iff.2 $ is_empty_pi.2 $
let ⟨a⟩ := mk_ne_zero_iff.1 heq in ⟨a, pempty.is_empty⟩

theorem power_ne_zero {a : cardinal} (b) : a ≠ 0 → a ^ b ≠ 0 :=
induction_on₂ a b $ λ α β h,
let ⟨a⟩ := mk_ne_zero_iff.1 h in mk_ne_zero_iff.2 ⟨λ _, a⟩

theorem mul_power {a b c : cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
induction_on₃ a b c $ λ α β γ, mk_congr $ equiv.arrow_prod_equiv_prod_arrow α β γ

theorem power_mul {a b c : cardinal} : a ^ (b * c) = (a ^ b) ^ c :=
by { rw [mul_comm b c], exact induction_on₃ a b c (λ α β γ, mk_congr $ equiv.curry γ β α) }

@[simp] lemma pow_cast_right (a : cardinal.{u}) (n : ℕ) : (a ^ (↑n : cardinal.{u})) = a ^ℕ n :=
rfl

@[simp] theorem lift_one : lift 1 = 1 :=
mk_congr $ equiv.ulift.trans equiv.punit_equiv_punit

@[simp] theorem lift_add (a b) : lift (a + b) = lift a + lift b :=
induction_on₂ a b $ λ α β,
mk_congr $ equiv.ulift.trans (equiv.sum_congr equiv.ulift equiv.ulift).symm

@[simp] theorem lift_mul (a b) : lift (a * b) = lift a * lift b :=
induction_on₂ a b $ λ α β,
mk_congr $ equiv.ulift.trans (equiv.prod_congr equiv.ulift equiv.ulift).symm

@[simp] theorem lift_bit0 (a : cardinal) : lift (bit0 a) = bit0 (lift a) :=
lift_add a a

@[simp] theorem lift_bit1 (a : cardinal) : lift (bit1 a) = bit1 (lift a) :=
by simp [bit1]

theorem lift_two : lift.{u v} 2 = 2 := by simp

@[simp] theorem mk_set {α : Type u} : #(set α) = 2 ^ #α := by simp [set, mk_arrow]

/-- A variant of `cardinal.mk_set` expressed in terms of a `set` instead of a `Type`. -/
@[simp] theorem mk_powerset {α : Type u} (s : set α) : #↥(𝒫 s) = 2 ^ #↥s :=
(mk_congr (equiv.set.powerset s)).trans mk_set

theorem lift_two_power (a) : lift (2 ^ a) = 2 ^ lift a := by simp

section order_properties
open sum

protected theorem zero_le : ∀ a : cardinal, 0 ≤ a :=
by rintro ⟨α⟩; exact ⟨embedding.of_is_empty⟩

private theorem add_le_add' : ∀ {a b c d : cardinal}, a ≤ b → c ≤ d → a + c ≤ b + d :=
by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩; exact ⟨e₁.sum_map e₂⟩

instance add_covariant_class : covariant_class cardinal cardinal (+) (≤) :=
⟨λ a b c, add_le_add' le_rfl⟩

instance add_swap_covariant_class : covariant_class cardinal cardinal (swap (+)) (≤) :=
⟨λ a b c h, add_le_add' h le_rfl⟩

instance : canonically_ordered_comm_semiring cardinal.{u} :=
{ bot                   := 0,
  bot_le                := cardinal.zero_le,
  add_le_add_left       := λ a b, add_le_add_left,
  le_iff_exists_add     := λ a b, ⟨induction_on₂ a b $ λ α β ⟨⟨f, hf⟩⟩,
    have (α ⊕ ((range f)ᶜ : set β)) ≃ β, from
      (equiv.sum_congr (equiv.of_injective f hf) (equiv.refl _)).trans $
      (equiv.set.sum_compl (range f)),
    ⟨#↥(range f)ᶜ, mk_congr this.symm⟩,
    λ ⟨c, e⟩, add_zero a ▸ e.symm ▸ add_le_add_left (cardinal.zero_le _) _⟩,
  eq_zero_or_eq_zero_of_mul_eq_zero := λ a b, induction_on₂ a b $ λ α β,
    by simpa only [mul_def, mk_eq_zero_iff, is_empty_prod] using id,
  ..cardinal.comm_semiring, ..cardinal.partial_order }

@[simp] theorem zero_lt_one : (0 : cardinal) < 1 :=
lt_of_le_of_ne (zero_le _) zero_ne_one

lemma zero_power_le (c : cardinal.{u}) : (0 : cardinal.{u}) ^ c ≤ 1 :=
by { by_cases h : c = 0, rw [h, power_zero], rw [zero_power h], apply zero_le }

theorem power_le_power_left : ∀ {a b c : cardinal}, a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c :=
by rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ hα ⟨e⟩; exact
  let ⟨a⟩ := mk_ne_zero_iff.1 hα in
  ⟨@embedding.arrow_congr_left _ _ _ ⟨a⟩ e⟩

theorem self_le_power (a : cardinal) {b : cardinal} (hb : 1 ≤ b) : a ≤ a ^ b :=
begin
  rcases eq_or_ne a 0 with rfl|ha,
  { exact zero_le _ },
  { convert power_le_power_left ha hb, exact power_one.symm }
end

/-- **Cantor's theorem** -/
theorem cantor (a : cardinal.{u}) : a < 2 ^ a :=
begin
  induction a using cardinal.induction_on with α,
  rw [← mk_set],
  refine ⟨⟨⟨singleton, λ a b, singleton_eq_singleton_iff.1⟩⟩, _⟩,
  rintro ⟨⟨f, hf⟩⟩,
  exact cantor_injective f hf
end

instance : no_max_order cardinal.{u} :=
{ exists_gt := λ a, ⟨_, cantor a⟩, ..cardinal.partial_order }

instance : canonically_linear_ordered_add_monoid cardinal.{u} :=
{ le_total     := by { rintros ⟨α⟩ ⟨β⟩, apply embedding.total },
  decidable_le := classical.dec_rel _,
  ..(infer_instance : canonically_ordered_add_monoid cardinal),
  ..cardinal.partial_order }

-- short-circuit type class inference
instance : distrib_lattice cardinal.{u} := by apply_instance

theorem one_lt_iff_nontrivial {α : Type u} : 1 < #α ↔ nontrivial α :=
by rw [← not_le, le_one_iff_subsingleton, ← not_nontrivial_iff_subsingleton, not_not]

theorem power_le_max_power_one {a b c : cardinal} (h : b ≤ c) : a ^ b ≤ max (a ^ c) 1 :=
begin
  by_cases ha : a = 0,
  simp [ha, zero_power_le],
  exact (power_le_power_left ha h).trans (le_max_left _ _)
end

theorem power_le_power_right {a b c : cardinal} : a ≤ b → a ^ c ≤ b ^ c :=
induction_on₃ a b c $ λ α β γ ⟨e⟩, ⟨embedding.arrow_congr_right e⟩

end order_properties

protected theorem lt_wf : @well_founded cardinal.{u} (<) :=
⟨λ a, classical.by_contradiction $ λ h, begin
  let ι := {c : cardinal // ¬ acc (<) c},
  let f : ι → cardinal := subtype.val,
  haveI hι : nonempty ι := ⟨⟨_, h⟩⟩,
  obtain ⟨⟨c : cardinal, hc : ¬acc (<) c⟩, ⟨h_1 : Π j, (f ⟨c, hc⟩).out ↪ (f j).out⟩⟩ :=
    embedding.min_injective (λ i, (f i).out),
  apply hc (acc.intro _ (λ j h', classical.by_contradiction (λ hj, h'.2 _))),
  have : #_ ≤ #_ := ⟨h_1 ⟨j, hj⟩⟩,
  simpa only [f, mk_out] using this
end⟩

instance : has_well_founded cardinal.{u} := ⟨(<), cardinal.lt_wf⟩

instance : conditionally_complete_linear_order_bot cardinal :=
cardinal.lt_wf.conditionally_complete_linear_order_with_bot 0 $ (cardinal.zero_le _).antisymm $
  not_lt.1 (cardinal.lt_wf.not_lt_min set.univ ⟨0, mem_univ _⟩ (mem_univ 0))

instance wo : @is_well_order cardinal.{u} (<) := ⟨cardinal.lt_wf⟩

@[simp] theorem Inf_empty : Inf (∅ : set cardinal.{u}) = 0 :=
dif_neg not_nonempty_empty

/-- Note that the successor of `c` is not the same as `c + 1` except in the case of finite `c`. -/
instance : succ_order cardinal :=
succ_order.of_succ_le_iff (λ c, Inf {c' | c < c'})
  (λ a b, ⟨lt_of_lt_of_le $ Inf_mem $ exists_gt a, cInf_le'⟩)

theorem succ_def (c : cardinal) : succ c = Inf {c' | c < c'} := rfl

theorem add_one_le_succ (c : cardinal.{u}) : c + 1 ≤ succ c :=
begin
  refine (le_cInf_iff'' (exists_gt c)).2 (λ b hlt, _),
  rcases ⟨b, c⟩ with ⟨⟨β⟩, ⟨γ⟩⟩,
  cases le_of_lt hlt with f,
  have : ¬ surjective f := λ hn, (not_le_of_lt hlt) (mk_le_of_surjective hn),
  simp only [surjective, not_forall] at this,
  rcases this with ⟨b, hb⟩,
  calc #γ + 1 = #(option γ) : mk_option.symm
          ... ≤ #β          : (f.option_elim b hb).cardinal_le
end

lemma succ_pos : ∀ c : cardinal, 0 < succ c := bot_lt_succ

lemma succ_ne_zero (c : cardinal) : succ c ≠ 0 := (succ_pos _).ne'

/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
def sum {ι} (f : ι → cardinal) : cardinal := mk Σ i, (f i).out

theorem le_sum {ι} (f : ι → cardinal) (i) : f i ≤ sum f :=
by rw ← quotient.out_eq (f i); exact
⟨⟨λ a, ⟨i, a⟩, λ a b h, eq_of_heq $ by injection h⟩⟩

@[simp] theorem mk_sigma {ι} (f : ι → Type*) : #(Σ i, f i) = sum (λ i, #(f i)) :=
mk_congr $ equiv.sigma_congr_right $ λ i, out_mk_equiv.symm

@[simp] theorem sum_const (ι : Type u) (a : cardinal.{v}) :
  sum (λ i : ι, a) = lift.{v} (#ι) * lift.{u} a :=
induction_on a $ λ α, mk_congr $
  calc (Σ i : ι, quotient.out (#α)) ≃ ι × quotient.out (#α) : equiv.sigma_equiv_prod _ _
  ... ≃ ulift ι × ulift α : equiv.ulift.symm.prod_congr (out_mk_equiv.trans equiv.ulift.symm)

theorem sum_const' (ι : Type u) (a : cardinal.{u}) : sum (λ _:ι, a) = #ι * a := by simp

@[simp] theorem sum_add_distrib {ι} (f g : ι → cardinal) :
  sum (f + g) = sum f + sum g :=
by simpa only [mk_sigma, mk_sum, mk_out, lift_id] using
  mk_congr (equiv.sigma_sum_distrib (quotient.out ∘ f) (quotient.out ∘ g))

@[simp] theorem sum_add_distrib' {ι} (f g : ι → cardinal) :
  cardinal.sum (λ i, f i + g i) = sum f + sum g :=
sum_add_distrib f g

@[simp] theorem lift_sum {ι : Type u} (f : ι → cardinal.{v}) :
  cardinal.lift.{w} (cardinal.sum f) = cardinal.sum (λ i, cardinal.lift.{w} (f i)) :=
equiv.cardinal_eq $ equiv.ulift.trans $ equiv.sigma_congr_right $ λ a, nonempty.some $
  by rw [←lift_mk_eq, mk_out, mk_out, lift_lift]

theorem sum_le_sum {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : sum f ≤ sum g :=
⟨(embedding.refl _).sigma_map $ λ i, classical.choice $
  by have := H i; rwa [← quot.out_eq (f i), ← quot.out_eq (g i)] at this⟩

lemma mk_le_mk_mul_of_mk_preimage_le {c : cardinal} (f : α → β) (hf : ∀ b : β, #(f ⁻¹' {b}) ≤ c) :
  #α ≤ #β * c :=
by simpa only [←mk_congr (@equiv.sigma_fiber_equiv α β f), mk_sigma, ←sum_const']
  using sum_le_sum _ _ hf

/-- The range of an indexed cardinal function, whose outputs live in a higher universe than the
    inputs, is always bounded above. -/
theorem bdd_above_range {ι : Type u} (f : ι → cardinal.{max u v}) : bdd_above (set.range f) :=
⟨_, by { rintros a ⟨i, rfl⟩, exact le_sum f i }⟩

instance (a : cardinal.{u}) : small.{u} (set.Iic a) :=
begin
  rw ←mk_out a,
  apply @small_of_surjective (set a.out) (Iic (#a.out)) _ (λ x, ⟨#x, mk_set_le x⟩),
  rintro ⟨x, hx⟩,
  simpa using le_mk_iff_exists_set.1 hx
end

/-- A set of cardinals is bounded above iff it's small, i.e. it corresponds to an usual ZFC set. -/
theorem bdd_above_iff_small (s : set cardinal.{u}) : bdd_above s ↔ small.{u} s :=
⟨λ ⟨a, ha⟩, @small_subset _ (Iic a) s (λ x h, ha h) _, begin
  rintro ⟨ι, ⟨e⟩⟩,
  suffices : range (λ x : ι, (e.symm x).1) = s,
  { rw ←this,
    apply bdd_above_range.{u u} },
  ext x,
  refine ⟨_, λ hx, ⟨e ⟨x, hx⟩, _⟩⟩,
  { rintro ⟨a, rfl⟩,
    exact (e.symm a).prop },
  { simp_rw [subtype.val_eq_coe, equiv.symm_apply_apply], refl }
end⟩

/-- The indexed supremum of cardinals is the smallest cardinal above
  everything in the family. -/
def sup {ι : Type u} (f : ι → cardinal.{max u v}) : cardinal :=
supr f

theorem le_sup {ι} (f : ι → cardinal.{max u v}) (i) : f i ≤ sup f :=
le_csupr (bdd_above_range f) i

theorem sup_le_iff {ι} {f : ι → cardinal} {a} : sup f ≤ a ↔ ∀ i, f i ≤ a :=
csupr_le_iff' (bdd_above_range f)

theorem sup_le {ι} {f : ι → cardinal} {a} : (∀ i, f i ≤ a) → sup f ≤ a :=
sup_le_iff.2

theorem sup_le_sup {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : sup f ≤ sup g :=
sup_le $ λ i, (H i).trans (le_sup _ _)

theorem sup_le_sum {ι} (f : ι → cardinal) : sup f ≤ sum f :=
sup_le $ le_sum _

theorem sum_le_sup {ι : Type u} (f : ι → cardinal.{u}) : sum f ≤ #ι * sup.{u u} f :=
by rw ← sum_const'; exact sum_le_sum _ _ (le_sup _)

theorem sum_le_sup_lift {ι : Type u} (f : ι → cardinal.{max u v}) :
  sum f ≤ (#ι).lift * sup.{u v} f :=
begin
  rw [←(sup f).lift_id, ←lift_umax, lift_umax.{(max u v) u}, ←sum_const],
  exact sum_le_sum _ _ (le_sup _)
end

theorem sum_nat_eq_add_sum_succ (f : ℕ → cardinal.{u}) :
  cardinal.sum f = f 0 + cardinal.sum (λ i, f (i + 1)) :=
begin
  refine (equiv.sigma_nat_succ (λ i, quotient.out (f i))).cardinal_eq.trans _,
  simp only [mk_sum, mk_out, lift_id, mk_sigma],
end

@[simp] theorem sup_eq_zero {ι} {f : ι → cardinal} [is_empty ι] : sup f = 0 :=
by { rw ←nonpos_iff_eq_zero, exact sup_le is_empty_elim }

/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
def prod {ι : Type u} (f : ι → cardinal) : cardinal := #(Π i, (f i).out)

@[simp] theorem mk_pi {ι : Type u} (α : ι → Type v) : #(Π i, α i) = prod (λ i, #(α i)) :=
mk_congr $ equiv.Pi_congr_right $ λ i, out_mk_equiv.symm

@[simp] theorem prod_const (ι : Type u) (a : cardinal.{v}) :
  prod (λ i : ι, a) = lift.{u} a ^ lift.{v} (#ι) :=
induction_on a $ λ α, mk_congr $ equiv.Pi_congr equiv.ulift.symm $
  λ i, out_mk_equiv.trans equiv.ulift.symm

theorem prod_const' (ι : Type u) (a : cardinal.{u}) : prod (λ _:ι, a) = a ^ #ι :=
induction_on a $ λ α, (mk_pi _).symm

theorem prod_le_prod {ι} (f g : ι → cardinal) (H : ∀ i, f i ≤ g i) : prod f ≤ prod g :=
⟨embedding.Pi_congr_right $ λ i, classical.choice $
  by have := H i; rwa [← mk_out (f i), ← mk_out (g i)] at this⟩

@[simp] theorem prod_eq_zero {ι} (f : ι → cardinal.{u}) : prod f = 0 ↔ ∃ i, f i = 0 :=
by { lift f to ι → Type u using λ _, trivial, simp only [mk_eq_zero_iff, ← mk_pi, is_empty_pi] }

theorem prod_ne_zero {ι} (f : ι → cardinal) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 :=
by simp [prod_eq_zero]

@[simp] theorem lift_prod {ι : Type u} (c : ι → cardinal.{v}) :
  lift.{w} (prod c) = prod (λ i, lift.{w} (c i)) :=
begin
  lift c to ι → Type v using λ _, trivial,
  simp only [← mk_pi, ← mk_ulift],
  exact mk_congr (equiv.ulift.trans $ equiv.Pi_congr_right $ λ i, equiv.ulift.symm)
end

@[simp] theorem lift_Inf (s : set cardinal) : lift (Inf s) = Inf (lift '' s) :=
begin
  rcases eq_empty_or_nonempty s with rfl | hs,
  { simp },
  { exact lift_monotone.map_Inf hs }
end

theorem lift_down {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b ≤ lift a → ∃ a', lift a' = b :=
induction_on₂ a b $ λ α β,
by rw [← lift_id (#β), ← lift_umax, ← lift_umax.{u v}, lift_mk_le]; exact
λ ⟨f⟩, ⟨#(set.range f), eq.symm $ lift_mk_eq.2
  ⟨embedding.equiv_of_surjective
    (embedding.cod_restrict _ f set.mem_range_self)
    $ λ ⟨a, ⟨b, e⟩⟩, ⟨b, subtype.eq e⟩⟩⟩

theorem le_lift_iff {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
⟨λ h, let ⟨a', e⟩ := lift_down h in ⟨a', e, lift_le.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
⟨λ h, let ⟨a', e⟩ := lift_down h.le in ⟨a', e, lift_lt.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_lt.2 h⟩

@[simp] theorem lift_succ (a) : lift (succ a) = succ (lift a) :=
le_antisymm
  (le_of_not_gt $ λ h, begin
    rcases lt_lift_iff.1 h with ⟨b, e, h⟩,
    rw [lt_succ_iff, ← lift_le, e] at h,
    exact h.not_lt (lt_succ _)
  end)
  (succ_le_of_lt $ lift_lt.2 $ lt_succ a)

@[simp] theorem lift_umax_eq {a : cardinal.{u}} {b : cardinal.{v}} :
  lift.{max v w} a = lift.{max u w} b ↔ lift.{v} a = lift.{u} b :=
by rw [←lift_lift, ←lift_lift, lift_inj]

@[simp] theorem lift_min {a b : cardinal} : lift (min a b) = min (lift a) (lift b) :=
lift_monotone.map_min

@[simp] theorem lift_max {a b : cardinal} : lift (max a b) = max (lift a) (lift b) :=
lift_monotone.map_max

protected lemma le_sup_iff {ι : Type v} {f : ι → cardinal.{max v w}} {c : cardinal} :
  (c ≤ sup f) ↔ (∀ b, (∀ i, f i ≤ b) → c ≤ b) :=
⟨λ h b hb, h.trans (sup_le hb), λ h, h _ $ le_sup f⟩

/-- The lift of a supremum is the supremum of the lifts. -/
lemma lift_sup {ι : Type v} (f : ι → cardinal.{max v w}) :
  lift.{u} (sup.{v w} f) = sup.{v (max u w)} (λ i : ι, lift.{u} (f i)) :=
begin
  apply le_antisymm,
  { rw [cardinal.le_sup_iff], intros c hc, by_contra h,
    obtain ⟨d, rfl⟩ := cardinal.lift_down (not_le.mp h).le,
    simp only [lift_le, sup_le_iff] at h hc,
    exact h hc },
  { simp only [cardinal.sup_le, lift_le, le_sup, implies_true_iff] }
end

/-- To prove that the lift of a supremum is bounded by some cardinal `t`,
it suffices to show that the lift of each cardinal is bounded by `t`. -/
lemma lift_sup_le {ι : Type v} (f : ι → cardinal.{max v w})
  (t : cardinal.{max u v w}) (w : ∀ i, lift.{u} (f i) ≤ t) :
  lift.{u} (sup f) ≤ t :=
by { rw lift_sup, exact sup_le w }

@[simp] lemma lift_sup_le_iff {ι : Type v} (f : ι → cardinal.{max v w}) (t : cardinal.{max u v w}) :
  lift.{u} (sup f) ≤ t ↔ ∀ i, lift.{u} (f i) ≤ t :=
⟨λ h i, (lift_le.mpr (le_sup f i)).trans h,
 λ h, lift_sup_le f t h⟩

universes v' w'

/--
To prove an inequality between the lifts to a common universe of two different supremums,
it suffices to show that the lift of each cardinal from the smaller supremum
if bounded by the lift of some cardinal from the larger supremum.
-/
lemma lift_sup_le_lift_sup
  {ι : Type v} {ι' : Type v'} (f : ι → cardinal.{max v w}) (f' : ι' → cardinal.{max v' w'})
  (g : ι → ι') (h : ∀ i, lift.{max v' w'} (f i) ≤ lift.{max v w} (f' (g i))) :
  lift.{max v' w'} (sup f) ≤ lift.{max v w} (sup f') :=
lift_sup_le.{max v' w'} f _ (λ i, (h i).trans $ by { rw lift_le, apply le_sup })

/-- A variant of `lift_sup_le_lift_sup` with universes specialized via `w = v` and `w' = v'`.
This is sometimes necessary to avoid universe unification issues. -/
lemma lift_sup_le_lift_sup'
  {ι : Type v} {ι' : Type v'} (f : ι → cardinal.{v}) (f' : ι' → cardinal.{v'})
  (g : ι → ι') (h : ∀ i, lift.{v'} (f i) ≤ lift.{v} (f' (g i))) :
  lift.{v'} (sup.{v v} f) ≤ lift.{v} (sup.{v' v'} f') :=
lift_sup_le_lift_sup f f' g h

/-- `ℵ₀` is the smallest infinite cardinal. -/
def aleph_0 : cardinal.{u} := lift (#ℕ)

localized "notation `ℵ₀` := cardinal.aleph_0" in cardinal

lemma mk_nat : #ℕ = ℵ₀ := (lift_id _).symm

theorem aleph_0_ne_zero : ℵ₀ ≠ 0 := mk_ne_zero _

theorem aleph_0_pos : 0 < ℵ₀ :=
pos_iff_ne_zero.2 aleph_0_ne_zero

@[simp] theorem lift_aleph_0 : lift ℵ₀ = ℵ₀ := lift_lift _

@[simp] theorem aleph_0_le_lift {c : cardinal.{u}} : ℵ₀ ≤ lift.{v} c ↔ ℵ₀ ≤ c :=
by rw [←lift_aleph_0, lift_le]

@[simp] theorem lift_le_aleph_0 {c : cardinal.{u}} : lift.{v} c ≤ ℵ₀ ↔ c ≤ ℵ₀ :=
by rw [←lift_aleph_0, lift_le]

/-! ### Properties about the cast from `ℕ` -/

@[simp] theorem mk_fin (n : ℕ) : #(fin n) = n := by simp

@[simp] theorem lift_nat_cast (n : ℕ) : lift.{u} (n : cardinal.{v}) = n :=
by induction n; simp *

@[simp] lemma lift_eq_nat_iff {a : cardinal.{u}} {n : ℕ} : lift.{v} a = n ↔ a = n :=
lift_injective.eq_iff' (lift_nat_cast n)

@[simp] lemma nat_eq_lift_iff {n : ℕ} {a : cardinal.{u}} :
  (n : cardinal) = lift.{v} a ↔ (n : cardinal) = a :=
by rw [←lift_nat_cast.{v} n, lift_inj]

theorem lift_mk_fin (n : ℕ) : lift (#(fin n)) = n := by simp

lemma mk_finset {α : Type u} {s : finset α} : #s = ↑(finset.card s) := by simp

theorem card_le_of_finset {α} (s : finset α) : (s.card : cardinal) ≤ #α :=
begin
  rw (_ : (s.card : cardinal) = #s),
  { exact ⟨function.embedding.subtype _⟩ },
  rw [cardinal.mk_fintype, fintype.card_coe]
end

@[simp, norm_cast] theorem nat_cast_pow {m n : ℕ} : (↑(pow m n) : cardinal) = m ^ n :=
by induction n; simp [pow_succ', power_add, *]

@[simp, norm_cast] theorem nat_cast_le {m n : ℕ} : (m : cardinal) ≤ n ↔ m ≤ n :=
begin
  rw [←lift_mk_fin, ←lift_mk_fin, lift_le],
  exact ⟨λ ⟨⟨f, hf⟩⟩, by simpa only [fintype.card_fin] using fintype.card_le_of_injective f hf,
    λ h, ⟨(fin.cast_le h).to_embedding⟩⟩
end

@[simp, norm_cast] theorem nat_cast_lt {m n : ℕ} : (m : cardinal) < n ↔ m < n :=
by simp [lt_iff_le_not_le, ←not_le]

instance : char_zero cardinal := ⟨strict_mono.injective $ λ m n, nat_cast_lt.2⟩

theorem nat_cast_inj {m n : ℕ} : (m : cardinal) = n ↔ m = n := nat.cast_inj

lemma nat_cast_injective : injective (coe : ℕ → cardinal) :=
nat.cast_injective

@[simp, norm_cast, priority 900] theorem nat_succ (n : ℕ) : (n.succ : cardinal) = succ n :=
(add_one_le_succ _).antisymm (succ_le_of_lt $ nat_cast_lt.2 $ nat.lt_succ_self _)

@[simp] theorem succ_zero : succ (0 : cardinal) = 1 := by norm_cast

theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ s : finset α, s.card ≤ n) : # α ≤ n :=
begin
  refine le_of_lt_succ (lt_of_not_ge $ λ hn, _),
  rw [←cardinal.nat_succ, ←lift_mk_fin n.succ] at hn,
  cases hn with f,
  refine (H $ finset.univ.map f).not_lt _,
  rw [finset.card_map, ←fintype.card, fintype.card_ulift, fintype.card_fin],
  exact n.lt_succ_self
end

theorem cantor' (a) {b : cardinal} (hb : 1 < b) : a < b ^ a :=
begin
  rw [←succ_le_iff, (by norm_cast : succ (1 : cardinal) = 2)] at hb,
  exact (cantor a).trans_le (power_le_power_right hb)
end

theorem one_le_iff_pos {c : cardinal} : 1 ≤ c ↔ 0 < c :=
by rw [←succ_zero, succ_le_iff]

theorem one_le_iff_ne_zero {c : cardinal} : 1 ≤ c ↔ c ≠ 0 :=
by rw [one_le_iff_pos, pos_iff_ne_zero]

theorem nat_lt_aleph_0 (n : ℕ) : (n : cardinal.{u}) < ℵ₀ :=
succ_le_iff.1 begin
  rw [←nat_succ, ←lift_mk_fin, aleph_0, lift_mk_le.{0 0 u}],
  exact ⟨⟨coe, λ a b, fin.ext⟩⟩
end

@[simp] theorem one_lt_aleph_0 : 1 < ℵ₀ := by simpa using nat_lt_aleph_0 1

theorem one_le_aleph_0 : 1 ≤ ℵ₀ := one_lt_aleph_0.le

theorem lt_aleph_0 {c : cardinal} : c < ℵ₀ ↔ ∃ n : ℕ, c = n :=
⟨λ h, begin
  rcases lt_lift_iff.1 h with ⟨c, rfl, h'⟩,
  rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩,
  suffices : S.finite,
  { lift S to finset ℕ using this,
    simp },
  contrapose! h',
  haveI := infinite.to_subtype h',
  exact ⟨infinite.nat_embedding S⟩
end, λ ⟨n, e⟩, e.symm ▸ nat_lt_aleph_0 _⟩

theorem aleph_0_le {c : cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c :=
⟨λ h n, (nat_lt_aleph_0 _).le.trans h,
 λ h, le_of_not_lt $ λ hn, begin
  rcases lt_aleph_0.1 hn with ⟨n, rfl⟩,
  exact (nat.lt_succ_self _).not_le (nat_cast_le.1 (h (n+1)))
end⟩

theorem lt_aleph_0_iff_fintype {α : Type u} : #α < ℵ₀ ↔ nonempty (fintype α) :=
lt_aleph_0.trans ⟨λ ⟨n, e⟩, begin
  rw [← lift_mk_fin n] at e,
  cases quotient.exact e with f,
  exact ⟨fintype.of_equiv _ f.symm⟩
end, λ ⟨_⟩, by exactI ⟨_, mk_fintype _⟩⟩

theorem lt_aleph_0_of_fintype (α : Type u) [fintype α] : #α < ℵ₀ :=
lt_aleph_0_iff_fintype.2 ⟨infer_instance⟩

theorem lt_aleph_0_iff_finite {α} {S : set α} : #S < ℵ₀ ↔ S.finite :=
lt_aleph_0_iff_fintype.trans finite_def.symm

instance can_lift_cardinal_nat : can_lift cardinal ℕ :=
⟨ coe, λ x, x < ℵ₀, λ x hx, let ⟨n, hn⟩ := lt_aleph_0.mp hx in ⟨n, hn.symm⟩⟩

theorem add_lt_aleph_0 {a b : cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a + b < ℵ₀ :=
match a, b, lt_aleph_0.1 ha, lt_aleph_0.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat.cast_add]; apply nat_lt_aleph_0
end

lemma add_lt_aleph_0_iff {a b : cardinal} : a + b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ :=
⟨λ h, ⟨(self_le_add_right _ _).trans_lt h, (self_le_add_left _ _).trans_lt h⟩,
  λ ⟨h1, h2⟩, add_lt_aleph_0 h1 h2⟩

lemma aleph_0_le_add_iff {a b : cardinal} : ℵ₀ ≤ a + b ↔ ℵ₀ ≤ a ∨ ℵ₀ ≤ b :=
by simp only [←not_lt, add_lt_aleph_0_iff, not_and_distrib]

/-- See also `cardinal.nsmul_lt_aleph_0_iff_of_ne_zero` if you already have `n ≠ 0`. -/
lemma nsmul_lt_aleph_0_iff {n : ℕ} {a : cardinal} : n • a < ℵ₀ ↔ n = 0 ∨ a < ℵ₀ :=
begin
  cases n,
  { simpa using nat_lt_aleph_0 0 },
  simp only [nat.succ_ne_zero, false_or],
  induction n with n ih,
  { simp },
  rw [succ_nsmul, add_lt_aleph_0_iff, ih, and_self]
end

/-- See also `cardinal.nsmul_lt_aleph_0_iff` for a hypothesis-free version. -/
lemma nsmul_lt_aleph_0_iff_of_ne_zero {n : ℕ} {a : cardinal} (h : n ≠ 0) : n • a < ℵ₀ ↔ a < ℵ₀ :=
nsmul_lt_aleph_0_iff.trans $ or_iff_right h

theorem mul_lt_aleph_0 {a b : cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a * b < ℵ₀ :=
match a, b, lt_aleph_0.1 ha, lt_aleph_0.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat.cast_mul]; apply nat_lt_aleph_0
end

lemma mul_lt_aleph_0_iff {a b : cardinal} : a * b < ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀ :=
begin
  refine ⟨λ h, _, _⟩,
  { by_cases ha : a = 0, { exact or.inl ha },
    right, by_cases hb : b = 0, { exact or.inl hb },
    right, rw [←ne, ←one_le_iff_ne_zero] at ha hb, split,
    { rw ←mul_one a,
      refine (mul_le_mul' le_rfl hb).trans_lt h },
    { rw ←one_mul b,
      refine (mul_le_mul' ha le_rfl).trans_lt h }},
  rintro (rfl|rfl|⟨ha,hb⟩); simp only [*, mul_lt_aleph_0, aleph_0_pos, zero_mul, mul_zero]
end

/-- See also `cardinal.aleph_0_le_mul_iff`. -/
lemma aleph_0_le_mul_iff {a b : cardinal} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ b ≠ 0 ∧ (ℵ₀ ≤ a ∨ ℵ₀ ≤ b) :=
let h := (@mul_lt_aleph_0_iff a b).not in
by rwa [not_lt, not_or_distrib, not_or_distrib, not_and_distrib, not_lt, not_lt] at h

/-- See also `cardinal.aleph_0_le_mul_iff'`. -/
lemma aleph_0_le_mul_iff' {a b : cardinal.{u}} : ℵ₀ ≤ a * b ↔ a ≠ 0 ∧ ℵ₀ ≤ b ∨ ℵ₀ ≤ a ∧ b ≠ 0 :=
begin
  have : ∀ {a : cardinal.{u}}, ℵ₀ ≤ a → a ≠ 0, from λ a, ne_bot_of_le_ne_bot aleph_0_ne_zero,
  simp only [aleph_0_le_mul_iff, and_or_distrib_left, and_iff_right_of_imp this,
    @and.left_comm (a ≠ 0)],
  simp only [and.comm, or.comm]
end

lemma mul_lt_aleph_0_iff_of_ne_zero {a b : cardinal} (ha : a ≠ 0) (hb : b ≠ 0) :
  a * b < ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀ :=
by simp [mul_lt_aleph_0_iff, ha, hb]

theorem power_lt_aleph_0 {a b : cardinal} (ha : a < ℵ₀) (hb : b < ℵ₀) : a ^ b < ℵ₀ :=
match a, b, lt_aleph_0.1 ha, lt_aleph_0.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat_cast_pow]; apply nat_lt_aleph_0
end

lemma eq_one_iff_unique {α : Type*} :
  #α = 1 ↔ subsingleton α ∧ nonempty α :=
calc #α = 1 ↔ #α ≤ 1 ∧ 1 ≤ #α : le_antisymm_iff
        ... ↔ subsingleton α ∧ nonempty α :
  le_one_iff_subsingleton.and (one_le_iff_ne_zero.trans mk_ne_zero_iff)

theorem infinite_iff {α : Type u} : infinite α ↔ ℵ₀ ≤ #α :=
by rw [←not_lt, lt_aleph_0_iff_fintype, not_nonempty_iff, is_empty_fintype]

@[simp] lemma aleph_0_le_mk (α : Type u) [infinite α] : ℵ₀ ≤ #α := infinite_iff.1 ‹_›

lemma encodable_iff {α : Type u} : nonempty (encodable α) ↔ #α ≤ ℵ₀ :=
⟨λ ⟨h⟩, ⟨(@encodable.encode' α h).trans equiv.ulift.symm.to_embedding⟩,
  λ ⟨h⟩, ⟨encodable.of_inj _ (h.trans equiv.ulift.to_embedding).injective⟩⟩

@[simp] lemma mk_le_aleph_0 [encodable α] : #α ≤ ℵ₀ := encodable_iff.1 ⟨‹_›⟩

lemma denumerable_iff {α : Type u} : nonempty (denumerable α) ↔ #α = ℵ₀ :=
⟨λ ⟨h⟩, mk_congr ((@denumerable.eqv α h).trans equiv.ulift.symm),
 λ h, by { cases quotient.exact h with f, exact ⟨denumerable.mk' $ f.trans equiv.ulift⟩ }⟩

@[simp] lemma mk_denumerable (α : Type u) [denumerable α] : #α = ℵ₀ :=
denumerable_iff.1 ⟨‹_›⟩

@[simp] lemma mk_set_le_aleph_0 (s : set α) : #s ≤ ℵ₀ ↔ countable s :=
begin
  rw [countable_iff_exists_injective], split,
  { rintro ⟨f'⟩, cases embedding.trans f' equiv.ulift.to_embedding with f hf, exact ⟨f, hf⟩ },
  { rintro ⟨f, hf⟩, exact ⟨embedding.trans ⟨f, hf⟩ equiv.ulift.symm.to_embedding⟩ }
end

@[simp] lemma mk_subtype_le_aleph_0 (p : α → Prop) : #{x // p x} ≤ ℵ₀ ↔ countable {x | p x} :=
mk_set_le_aleph_0 _

@[simp] lemma aleph_0_add_aleph_0 : ℵ₀ + ℵ₀ = ℵ₀ := mk_denumerable _

lemma aleph_0_mul_aleph_0 : ℵ₀ * ℵ₀ = ℵ₀ := mk_denumerable _

@[simp] lemma add_le_aleph_0 {c₁ c₂ : cardinal} : c₁ + c₂ ≤ ℵ₀ ↔ c₁ ≤ ℵ₀ ∧ c₂ ≤ ℵ₀ :=
⟨λ h, ⟨le_self_add.trans h, le_add_self.trans h⟩, λ h, aleph_0_add_aleph_0 ▸ add_le_add h.1 h.2⟩

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to 0. -/
def to_nat : zero_hom cardinal ℕ :=
⟨λ c, if h : c < aleph_0.{v} then classical.some (lt_aleph_0.1 h) else 0,
  begin
    have h : 0 < ℵ₀ := nat_lt_aleph_0 0,
    rw [dif_pos h, ← cardinal.nat_cast_inj, ← classical.some_spec (lt_aleph_0.1 h), nat.cast_zero],
  end⟩

lemma to_nat_apply_of_lt_aleph_0 {c : cardinal} (h : c < ℵ₀) :
  c.to_nat = classical.some (lt_aleph_0.1 h) :=
dif_pos h

lemma to_nat_apply_of_aleph_0_le {c : cardinal} (h : ℵ₀ ≤ c) : c.to_nat = 0 :=
dif_neg h.not_lt

lemma cast_to_nat_of_lt_aleph_0 {c : cardinal} (h : c < ℵ₀) : ↑c.to_nat = c :=
by rw [to_nat_apply_of_lt_aleph_0 h, ← classical.some_spec (lt_aleph_0.1 h)]

lemma cast_to_nat_of_aleph_0_le {c : cardinal} (h : ℵ₀ ≤ c) : ↑c.to_nat = (0 : cardinal) :=
by rw [to_nat_apply_of_aleph_0_le h, nat.cast_zero]

lemma to_nat_le_iff_le_of_lt_aleph_0 {c d : cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
  c.to_nat ≤ d.to_nat ↔ c ≤ d :=
by rw [←nat_cast_le, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]

lemma to_nat_lt_iff_lt_of_lt_aleph_0 {c d : cardinal} (hc : c < ℵ₀) (hd : d < ℵ₀) :
  c.to_nat < d.to_nat ↔ c < d :=
by rw [←nat_cast_lt, cast_to_nat_of_lt_aleph_0 hc, cast_to_nat_of_lt_aleph_0 hd]

lemma to_nat_le_of_le_of_lt_aleph_0 {c d : cardinal} (hd : d < ℵ₀) (hcd : c ≤ d) :
  c.to_nat ≤ d.to_nat :=
(to_nat_le_iff_le_of_lt_aleph_0 (hcd.trans_lt hd) hd).mpr hcd

lemma to_nat_lt_of_lt_of_lt_aleph_0 {c d : cardinal} (hd : d < ℵ₀) (hcd : c < d) :
  c.to_nat < d.to_nat :=
(to_nat_lt_iff_lt_of_lt_aleph_0 (hcd.trans hd) hd).mpr hcd

@[simp] lemma to_nat_cast (n : ℕ) : cardinal.to_nat n = n :=
begin
  rw [to_nat_apply_of_lt_aleph_0 (nat_lt_aleph_0 n), ← nat_cast_inj],
  exact (classical.some_spec (lt_aleph_0.1 (nat_lt_aleph_0 n))).symm,
end

/-- `to_nat` has a right-inverse: coercion. -/
lemma to_nat_right_inverse : function.right_inverse (coe : ℕ → cardinal) to_nat := to_nat_cast

lemma to_nat_surjective : surjective to_nat := to_nat_right_inverse.surjective

@[simp] lemma mk_to_nat_of_infinite [h : infinite α] : (#α).to_nat = 0 :=
dif_neg (infinite_iff.1 h).not_lt

lemma mk_to_nat_eq_card [fintype α] : (#α).to_nat = fintype.card α := by simp

@[simp] lemma zero_to_nat : to_nat 0 = 0 :=
by rw [←to_nat_cast 0, nat.cast_zero]

@[simp] lemma one_to_nat : to_nat 1 = 1 :=
by rw [←to_nat_cast 1, nat.cast_one]

@[simp] lemma to_nat_eq_one {c : cardinal} : to_nat c = 1 ↔ c = 1 :=
⟨λ h, (cast_to_nat_of_lt_aleph_0 (lt_of_not_ge (one_ne_zero ∘ h.symm.trans ∘
  to_nat_apply_of_aleph_0_le))).symm.trans ((congr_arg coe h).trans nat.cast_one),
  λ h, (congr_arg to_nat h).trans one_to_nat⟩

lemma to_nat_eq_one_iff_unique {α : Type*} : (#α).to_nat = 1 ↔ subsingleton α ∧ nonempty α :=
to_nat_eq_one.trans eq_one_iff_unique

@[simp] lemma to_nat_lift (c : cardinal.{v}) : (lift.{u v} c).to_nat = c.to_nat :=
begin
  apply nat_cast_injective,
  cases lt_or_ge c ℵ₀ with hc hc,
  { rw [cast_to_nat_of_lt_aleph_0, ←lift_nat_cast, cast_to_nat_of_lt_aleph_0 hc],
    rwa [←lift_aleph_0, lift_lt] },
  { rw [cast_to_nat_of_aleph_0_le, ←lift_nat_cast, cast_to_nat_of_aleph_0_le hc, lift_zero],
    rwa [←lift_aleph_0, lift_le] },
end

lemma to_nat_congr {β : Type v} (e : α ≃ β) : (#α).to_nat = (#β).to_nat :=
by rw [←to_nat_lift, lift_mk_eq.mpr ⟨e⟩, to_nat_lift]

@[simp] lemma to_nat_mul (x y : cardinal) : (x * y).to_nat = x.to_nat * y.to_nat :=
begin
  rcases eq_or_ne x 0 with rfl | hx1,
  { rw [zero_mul, zero_to_nat, zero_mul] },
  rcases eq_or_ne y 0 with rfl | hy1,
  { rw [mul_zero, zero_to_nat, mul_zero] },
  cases lt_or_le x ℵ₀ with hx2 hx2,
  { cases lt_or_le y ℵ₀ with hy2 hy2,
    { lift x to ℕ using hx2, lift y to ℕ using hy2,
      rw [← nat.cast_mul, to_nat_cast, to_nat_cast, to_nat_cast] },
    { rw [to_nat_apply_of_aleph_0_le hy2, mul_zero, to_nat_apply_of_aleph_0_le],
      exact aleph_0_le_mul_iff'.2 (or.inl ⟨hx1, hy2⟩) } },
  { rw [to_nat_apply_of_aleph_0_le hx2, zero_mul, to_nat_apply_of_aleph_0_le],
    exact aleph_0_le_mul_iff'.2 (or.inr ⟨hx2, hy1⟩) },
end

@[simp] lemma to_nat_add_of_lt_aleph_0 {a : cardinal.{u}} {b : cardinal.{v}}
  (ha : a < ℵ₀) (hb : b < ℵ₀) : ((lift.{v u} a) + (lift.{u v} b)).to_nat = a.to_nat + b.to_nat :=
begin
  apply cardinal.nat_cast_injective,
  replace ha : (lift.{v u} a) < ℵ₀ := by { rw ←lift_aleph_0, exact lift_lt.2 ha },
  replace hb : (lift.{u v} b) < ℵ₀ := by { rw ←lift_aleph_0, exact lift_lt.2 hb },
  rw [nat.cast_add, ←to_nat_lift.{v u} a, ←to_nat_lift.{u v} b, cast_to_nat_of_lt_aleph_0 ha,
    cast_to_nat_of_lt_aleph_0 hb, cast_to_nat_of_lt_aleph_0 (add_lt_aleph_0 ha hb)]
end

/-- This function sends finite cardinals to the corresponding natural, and infinite cardinals
  to `⊤`. -/
def to_enat : cardinal →+ enat :=
{ to_fun := λ c, if c < ℵ₀ then c.to_nat else ⊤,
  map_zero' := by simp [if_pos (zero_lt_one.trans one_lt_aleph_0)],
  map_add' := λ x y, begin
    by_cases hx : x < ℵ₀,
    { obtain ⟨x0, rfl⟩ := lt_aleph_0.1 hx,
      by_cases hy : y < ℵ₀,
      { obtain ⟨y0, rfl⟩ := lt_aleph_0.1 hy,
        simp only [add_lt_aleph_0 hx hy, hx, hy, to_nat_cast, if_true],
        rw [← nat.cast_add, to_nat_cast, nat.cast_add] },
      { rw [if_neg hy, if_neg, enat.add_top],
        contrapose! hy,
        apply le_add_self.trans_lt hy } },
    { rw [if_neg hx, if_neg, enat.top_add],
      contrapose! hx,
      apply le_self_add.trans_lt hx },
  end }

lemma to_enat_apply_of_lt_aleph_0 {c : cardinal} (h : c < ℵ₀) : c.to_enat = c.to_nat :=
if_pos h

lemma to_enat_apply_of_aleph_0_le {c : cardinal} (h : ℵ₀ ≤ c) : c.to_enat = ⊤ :=
if_neg h.not_lt

@[simp] lemma to_enat_cast (n : ℕ) : cardinal.to_enat n = n :=
by rw [to_enat_apply_of_lt_aleph_0 (nat_lt_aleph_0 n), to_nat_cast]

@[simp] lemma mk_to_enat_of_infinite [h : infinite α] : (#α).to_enat = ⊤ :=
to_enat_apply_of_aleph_0_le (infinite_iff.1 h)

lemma to_enat_surjective : surjective to_enat :=
λ x, enat.cases_on x ⟨ℵ₀, to_enat_apply_of_aleph_0_le le_rfl⟩ $ λ n, ⟨n, to_enat_cast n⟩

lemma mk_to_enat_eq_coe_card [fintype α] : (#α).to_enat = fintype.card α :=
by simp

lemma mk_int : #ℤ = ℵ₀ := mk_denumerable ℤ

lemma mk_pnat : #ℕ+ = ℵ₀ := mk_denumerable ℕ+

/-- **König's theorem** -/
theorem sum_lt_prod {ι} (f g : ι → cardinal) (H : ∀ i, f i < g i) : sum f < prod g :=
lt_of_not_ge $ λ ⟨F⟩, begin
  haveI : inhabited (Π (i : ι), (g i).out),
  { refine ⟨λ i, classical.choice $ mk_ne_zero_iff.1 _⟩,
    rw mk_out,
    exact (H i).ne_bot },
  let G := inv_fun F,
  have sG : surjective G := inv_fun_surjective F.2,
  choose C hc using show ∀ i, ∃ b, ∀ a, G ⟨i, a⟩ i ≠ b,
  { intro i,
    simp only [- not_exists, not_exists.symm, not_forall.symm],
    refine λ h, (H i).not_le _,
    rw [← mk_out (f i), ← mk_out (g i)],
    exact ⟨embedding.of_surjective _ h⟩ },
  exact (let ⟨⟨i, a⟩, h⟩ := sG C in hc i a (congr_fun h _))
end

@[simp] theorem mk_empty : #empty = 0 := mk_eq_zero _

@[simp] theorem mk_pempty : #pempty = 0 := mk_eq_zero _

@[simp] theorem mk_punit : #punit = 1 := mk_eq_one punit

theorem mk_unit : #unit = 1 := mk_punit

@[simp] theorem mk_singleton {α : Type u} (x : α) : #({x} : set α) = 1 :=
mk_eq_one _

@[simp] theorem mk_plift_true : #(plift true) = 1 := mk_eq_one _
@[simp] theorem mk_plift_false : #(plift false) = 0 := mk_eq_zero _

@[simp] theorem mk_vector (α : Type u) (n : ℕ) : #(vector α n) = (#α) ^ℕ n :=
(mk_congr (equiv.vector_equiv_fin α n)).trans $ by simp

theorem mk_list_eq_sum_pow (α : Type u) : #(list α) = sum (λ n : ℕ, (#α) ^ℕ n) :=
calc #(list α) = #(Σ n, vector α n) : mk_congr (equiv.sigma_fiber_equiv list.length).symm
... = sum (λ n : ℕ, (#α) ^ℕ n) : by simp

theorem mk_quot_le {α : Type u} {r : α → α → Prop} : #(quot r) ≤ #α :=
mk_le_of_surjective quot.exists_rep

theorem mk_quotient_le {α : Type u} {s : setoid α} : #(quotient s) ≤ #α :=
mk_quot_le

theorem mk_subtype_le_of_subset {α : Type u} {p q : α → Prop} (h : ∀ ⦃x⦄, p x → q x) :
  #(subtype p) ≤ #(subtype q) :=
⟨embedding.subtype_map (embedding.refl α) h⟩

@[simp] theorem mk_emptyc (α : Type u) : #(∅ : set α) = 0 := mk_eq_zero _

lemma mk_emptyc_iff {α : Type u} {s : set α} : #s = 0 ↔ s = ∅ :=
begin
  split,
  { intro h,
    rw mk_eq_zero_iff at h,
    exact eq_empty_iff_forall_not_mem.2 (λ x hx, h.elim' ⟨x, hx⟩) },
  { rintro rfl, exact mk_emptyc _ }
end

@[simp] theorem mk_univ {α : Type u} : #(@univ α) = #α :=
mk_congr (equiv.set.univ α)

theorem mk_image_le {α β : Type u} {f : α → β} {s : set α} : #(f '' s) ≤ #s :=
mk_le_of_surjective surjective_onto_image

theorem mk_image_le_lift {α : Type u} {β : Type v} {f : α → β} {s : set α} :
  lift.{u} (#(f '' s)) ≤ lift.{v} (#s) :=
lift_mk_le.{v u 0}.mpr ⟨embedding.of_surjective _ surjective_onto_image⟩

theorem mk_range_le {α β : Type u} {f : α → β} : #(range f) ≤ #α :=
mk_le_of_surjective surjective_onto_range

theorem mk_range_le_lift {α : Type u} {β : Type v} {f : α → β} :
  lift.{u} (#(range f)) ≤ lift.{v} (#α) :=
lift_mk_le.{v u 0}.mpr ⟨embedding.of_surjective _ surjective_onto_range⟩

lemma mk_range_eq (f : α → β) (h : injective f) : #(range f) = #α :=
mk_congr ((equiv.of_injective f h).symm)

lemma mk_range_eq_of_injective {α : Type u} {β : Type v} {f : α → β} (hf : injective f) :
  lift.{u} (#(range f)) = lift.{v} (#α) :=
lift_mk_eq'.mpr ⟨(equiv.of_injective f hf).symm⟩

lemma mk_range_eq_lift {α : Type u} {β : Type v} {f : α → β} (hf : injective f) :
  lift.{max u w} (# (range f)) = lift.{max v w} (# α) :=
lift_mk_eq.mpr ⟨(equiv.of_injective f hf).symm⟩

theorem mk_image_eq {α β : Type u} {f : α → β} {s : set α} (hf : injective f) :
  #(f '' s) = #s :=
mk_congr ((equiv.set.image f s hf).symm)

theorem mk_Union_le_sum_mk {α ι : Type u} {f : ι → set α} : #(⋃ i, f i) ≤ sum (λ i, #(f i)) :=
calc #(⋃ i, f i) ≤ #(Σ i, f i)        : mk_le_of_surjective (set.sigma_to_Union_surjective f)
              ... = sum (λ i, #(f i)) : mk_sigma _

theorem mk_Union_eq_sum_mk {α ι : Type u} {f : ι → set α} (h : ∀i j, i ≠ j → disjoint (f i) (f j)) :
  #(⋃ i, f i) = sum (λ i, #(f i)) :=
calc #(⋃ i, f i) = #(Σ i, f i)       : mk_congr (set.Union_eq_sigma_of_disjoint h)
              ... = sum (λi, #(f i)) : mk_sigma _

lemma mk_Union_le {α ι : Type u} (f : ι → set α) :
  #(⋃ i, f i) ≤ #ι * cardinal.sup.{u u} (λ i, #(f i)) :=
mk_Union_le_sum_mk.trans (sum_le_sup _)

lemma mk_sUnion_le {α : Type u} (A : set (set α)) :
  #(⋃₀ A) ≤ #A * cardinal.sup.{u u} (λ s : A, #s) :=
by { rw sUnion_eq_Union, apply mk_Union_le }

lemma mk_bUnion_le {ι α : Type u} (A : ι → set α) (s : set ι) :
  #(⋃ x ∈ s, A x) ≤ #s * cardinal.sup.{u u} (λ x : s, #(A x.1)) :=
by { rw bUnion_eq_Union, apply mk_Union_le }

lemma finset_card_lt_aleph_0 (s : finset α) : #(↑s : set α) < ℵ₀ :=
by { rw lt_aleph_0_iff_fintype, exact ⟨finset.subtype.fintype s⟩ }

theorem mk_eq_nat_iff_finset {α} {s : set α} {n : ℕ} :
  #s = n ↔ ∃ t : finset α, (t : set α) = s ∧ t.card = n :=
begin
  split,
  { intro h,
    lift s to finset α using lt_aleph_0_iff_finite.1 (h.symm ▸ nat_lt_aleph_0 n),
    simpa using h },
  { rintro ⟨t, rfl, rfl⟩,
    exact mk_finset }
end

theorem mk_union_add_mk_inter {α : Type u} {S T : set α} :
  #(S ∪ T : set α) + #(S ∩ T : set α) = #S + #T :=
quot.sound ⟨equiv.set.union_sum_inter S T⟩

/-- The cardinality of a union is at most the sum of the cardinalities
of the two sets. -/
lemma mk_union_le {α : Type u} (S T : set α) : #(S ∪ T : set α) ≤ #S + #T :=
@mk_union_add_mk_inter α S T ▸ self_le_add_right (#(S ∪ T : set α)) (#(S ∩ T : set α))

theorem mk_union_of_disjoint {α : Type u} {S T : set α} (H : disjoint S T) :
  #(S ∪ T : set α) = #S + #T :=
quot.sound ⟨equiv.set.union H⟩

theorem mk_insert {α : Type u} {s : set α} {a : α} (h : a ∉ s) :
  #(insert a s : set α) = #s + 1 :=
by { rw [← union_singleton, mk_union_of_disjoint, mk_singleton], simpa }

lemma mk_sum_compl {α} (s : set α) : #s + #(sᶜ : set α) = #α :=
mk_congr (equiv.set.sum_compl s)

lemma mk_le_mk_of_subset {α} {s t : set α} (h : s ⊆ t) : #s ≤ #t :=
⟨set.embedding_of_subset s t h⟩

lemma mk_subtype_mono {p q : α → Prop} (h : ∀ x, p x → q x) : #{x // p x} ≤ #{x // q x} :=
⟨embedding_of_subset _ _ h⟩

lemma mk_union_le_aleph_0 {α} {P Q : set α} : #((P ∪ Q : set α)) ≤ ℵ₀ ↔ #P ≤ ℵ₀ ∧ #Q ≤ ℵ₀ :=
by simp

lemma mk_image_eq_lift {α : Type u} {β : Type v} (f : α → β) (s : set α) (h : injective f) :
  lift.{u} (#(f '' s)) = lift.{v} (#s) :=
lift_mk_eq.{v u 0}.mpr ⟨(equiv.set.image f s h).symm⟩

lemma mk_image_eq_of_inj_on_lift {α : Type u} {β : Type v} (f : α → β) (s : set α)
  (h : inj_on f s) : lift.{u} (#(f '' s)) = lift.{v} (#s) :=
lift_mk_eq.{v u 0}.mpr ⟨(equiv.set.image_of_inj_on f s h).symm⟩

lemma mk_image_eq_of_inj_on {α β : Type u} (f : α → β) (s : set α) (h : inj_on f s) :
  #(f '' s) = #s :=
mk_congr ((equiv.set.image_of_inj_on f s h).symm)

lemma mk_subtype_of_equiv {α β : Type u} (p : β → Prop) (e : α ≃ β) :
  #{a : α // p (e a)} = #{b : β // p b} :=
mk_congr (equiv.subtype_equiv_of_subtype e)

lemma mk_sep (s : set α) (t : α → Prop) : #({ x ∈ s | t x } : set α) = #{ x : s | t x.1 } :=
mk_congr (equiv.set.sep s t)

lemma mk_preimage_of_injective_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
  (h : injective f) : lift.{v} (#(f ⁻¹' s)) ≤ lift.{u} (#s) :=
begin
  rw lift_mk_le.{u v 0}, use subtype.coind (λ x, f x.1) (λ x, x.2),
  apply subtype.coind_injective, exact h.comp subtype.val_injective
end

lemma mk_preimage_of_subset_range_lift {α : Type u} {β : Type v} (f : α → β) (s : set β)
  (h : s ⊆ range f) : lift.{u} (#s) ≤ lift.{v} (#(f ⁻¹' s)) :=
begin
  rw lift_mk_le.{v u 0},
  refine ⟨⟨_, _⟩⟩,
  { rintro ⟨y, hy⟩, rcases classical.subtype_of_exists (h hy) with ⟨x, rfl⟩, exact ⟨x, hy⟩ },
  rintro ⟨y, hy⟩ ⟨y', hy'⟩, dsimp,
  rcases classical.subtype_of_exists (h hy) with ⟨x, rfl⟩,
  rcases classical.subtype_of_exists (h hy') with ⟨x', rfl⟩,
  simp, intro hxx', rw hxx'
end

lemma mk_preimage_of_injective_of_subset_range_lift {β : Type v} (f : α → β) (s : set β)
  (h : injective f) (h2 : s ⊆ range f) : lift.{v} (#(f ⁻¹' s)) = lift.{u} (#s) :=
le_antisymm (mk_preimage_of_injective_lift f s h) (mk_preimage_of_subset_range_lift f s h2)

lemma mk_preimage_of_injective (f : α → β) (s : set β) (h : injective f) :
  #(f ⁻¹' s) ≤ #s :=
by { convert mk_preimage_of_injective_lift.{u u} f s h using 1; rw [lift_id] }

lemma mk_preimage_of_subset_range (f : α → β) (s : set β)
  (h : s ⊆ range f) : #s ≤ #(f ⁻¹' s) :=
by { convert mk_preimage_of_subset_range_lift.{u u} f s h using 1; rw [lift_id] }

lemma mk_preimage_of_injective_of_subset_range (f : α → β) (s : set β)
  (h : injective f) (h2 : s ⊆ range f) : #(f ⁻¹' s) = #s :=
by { convert mk_preimage_of_injective_of_subset_range_lift.{u u} f s h h2 using 1; rw [lift_id] }

lemma mk_subset_ge_of_subset_image_lift {α : Type u} {β : Type v} (f : α → β) {s : set α}
  {t : set β} (h : t ⊆ f '' s) :
    lift.{u} (#t) ≤ lift.{v} (#({ x ∈ s | f x ∈ t } : set α)) :=
by { rw [image_eq_range] at h, convert mk_preimage_of_subset_range_lift _ _ h using 1,
     rw [mk_sep], refl }

lemma mk_subset_ge_of_subset_image (f : α → β) {s : set α} {t : set β} (h : t ⊆ f '' s) :
  #t ≤ #({ x ∈ s | f x ∈ t } : set α) :=
by { rw [image_eq_range] at h, convert mk_preimage_of_subset_range _ _ h using 1,
     rw [mk_sep], refl }

theorem le_mk_iff_exists_subset {c : cardinal} {α : Type u} {s : set α} :
  c ≤ #s ↔ ∃ p : set α, p ⊆ s ∧ #p = c :=
begin
  rw [le_mk_iff_exists_set, ←subtype.exists_set_subtype],
  apply exists_congr, intro t, rw [mk_image_eq], apply subtype.val_injective
end

lemma two_le_iff : (2 : cardinal) ≤ #α ↔ ∃x y : α, x ≠ y :=
begin
  split,
  { rintro ⟨f⟩, refine ⟨f $ sum.inl ⟨⟩, f $ sum.inr ⟨⟩, _⟩, intro h, cases f.2 h },
  { rintro ⟨x, y, h⟩, by_contra h',
    rw [not_le, ←nat.cast_two, nat_succ, lt_succ_iff, nat.cast_one, le_one_iff_subsingleton] at h',
    apply h, exactI subsingleton.elim _ _ }
end

lemma two_le_iff' (x : α) : (2 : cardinal) ≤ #α ↔ ∃y : α, x ≠ y :=
begin
  rw [two_le_iff],
  split,
  { rintro ⟨y, z, h⟩, refine classical.by_cases (λ(h' : x = y), _) (λ h', ⟨y, h'⟩),
    rw [←h'] at h, exact ⟨z, h⟩ },
  { rintro ⟨y, h⟩, exact ⟨x, y, h⟩ }
end

lemma exists_not_mem_of_length_le {α : Type*} (l : list α) (h : ↑l.length < # α) :
  ∃ (z : α), z ∉ l :=
begin
  contrapose! h,
  calc # α = # (set.univ : set α) : mk_univ.symm
    ... ≤ # l.to_finset           : mk_le_mk_of_subset (λ x _, list.mem_to_finset.mpr (h x))
    ... = l.to_finset.card        : cardinal.mk_finset
    ... ≤ l.length                : cardinal.nat_cast_le.mpr (list.to_finset_card_le l),
end

lemma three_le {α : Type*} (h : 3 ≤ # α) (x : α) (y : α) :
  ∃ (z : α), z ≠ x ∧ z ≠ y :=
begin
  have : ↑(3 : ℕ) ≤ # α, simpa using h,
  have : ↑(2 : ℕ) < # α, rwa [← succ_le_iff, ← cardinal.nat_succ],
  have := exists_not_mem_of_length_le [x, y] this,
  simpa [not_or_distrib] using this,
end

/-- The function α^{<β}, defined to be sup_{γ < β} α^γ.
  We index over {s : set β.out // #s < β } instead of {γ // γ < β}, because the latter lives in a
  higher universe -/
def powerlt (α β : cardinal.{u}) : cardinal.{u} :=
sup.{u u} (λ(s : {s : set β.out // #s < β}), α ^ mk.{u} s)

infix ` ^< `:80 := powerlt

theorem powerlt_aux {c c' : cardinal} (h : c < c') :
  ∃ (s : {s : set c'.out // #s < c'}), #s = c :=
begin
  cases out_embedding.mp h.le with f,
  have : #↥(range ⇑f) = c, { rwa [mk_range_eq, mk, quotient.out_eq c], exact f.2 },
  exact ⟨⟨range f, by convert h⟩, this⟩
end

lemma le_powerlt {c₁ c₂ c₃ : cardinal} (h : c₂ < c₃) : c₁ ^ c₂ ≤ c₁ ^< c₃ :=
by { rcases powerlt_aux h with ⟨s, rfl⟩, apply le_sup _ s }

lemma powerlt_le {c₁ c₂ c₃ : cardinal} : c₁ ^< c₂ ≤ c₃ ↔ ∀(c₄ < c₂), c₁ ^ c₄ ≤ c₃ :=
begin
  rw [powerlt, sup_le_iff],
  split,
  { intros h c₄ hc₄, rcases powerlt_aux hc₄ with ⟨s, rfl⟩, exact h s },
  intros h s, exact h _ s.2
end

lemma powerlt_le_powerlt_left {a b c : cardinal} (h : b ≤ c) : a ^< b ≤ a ^< c :=
by { rw [powerlt, sup_le_iff], exact λ ⟨s, hs⟩, le_powerlt (hs.trans_le h) }

lemma powerlt_succ {c₁ c₂ : cardinal} (h : c₁ ≠ 0) : c₁ ^< (succ c₂) = c₁ ^ c₂ :=
begin
  apply le_antisymm,
  { rw powerlt_le, intros c₃ h2, apply power_le_power_left h, rwa [←lt_succ_iff] },
  { apply le_powerlt, apply lt_succ }
end

lemma powerlt_max {c₁ c₂ c₃ : cardinal} : c₁ ^< max c₂ c₃ = max (c₁ ^< c₂) (c₁ ^< c₃) :=
by { cases le_total c₂ c₃; simp only [max_eq_left, max_eq_right, h, powerlt_le_powerlt_left] }

lemma zero_powerlt {a : cardinal} (h : a ≠ 0) : 0 ^< a = 1 :=
begin
  apply le_antisymm,
  { rw [powerlt_le], intros c hc, apply zero_power_le },
  convert le_powerlt (pos_iff_ne_zero.2 h), rw [power_zero]
end

lemma powerlt_zero {a : cardinal} : a ^< 0 = 0 :=
begin
  convert sup_eq_zero,
  exact subtype.is_empty_of_false (λ x, (zero_le _).not_lt),
end

end cardinal
