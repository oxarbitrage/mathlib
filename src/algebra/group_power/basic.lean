/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import algebra.hom.ring
import data.nat.basic

/-!
# Power operations on monoids and groups

The power operation on monoids and groups.
We separate this from group, because it depends on `ℕ`,
which in turn depends on other parts of algebra.

This module contains lemmas about `a ^ n` and `n • a`, where `n : ℕ` or `n : ℤ`.
Further lemmas can be found in `algebra.group_power.lemmas`.

The analogous results for groups with zero can be found in `algebra.group_with_zero.power`.

## Notation

- `a ^ n` is used as notation for `has_pow.pow a n`; in this file `n : ℕ` or `n : ℤ`.
- `n • a` is used as notation for `has_scalar.smul n a`; in this file `n : ℕ` or `n : ℤ`.

## Implementation details

We adopt the convention that `0^0 = 1`.
-/

universes u v w x y z u₁ u₂

variables {α : Type*} {M : Type u} {N : Type v} {G : Type w} {H : Type x} {A : Type y} {B : Type z}
  {R : Type u₁} {S : Type u₂}

/-!
### Commutativity

First we prove some facts about `semiconj_by` and `commute`. They do not require any theory about
`pow` and/or `nsmul` and will be useful later in this file.
-/

section has_pow
variables [has_pow M ℕ]

@[simp] lemma pow_ite (P : Prop) [decidable P] (a : M) (b c : ℕ) :
  a ^ (if P then b else c) = if P then a ^ b else a ^ c :=
by split_ifs; refl

@[simp] lemma ite_pow (P : Prop) [decidable P] (a b : M) (c : ℕ) :
  (if P then a else b) ^ c = if P then a ^ c else b ^ c :=
by split_ifs; refl

end has_pow

section monoid
variables [monoid M] [monoid N] [add_monoid A] [add_monoid B]

@[simp, to_additive one_nsmul]
theorem pow_one (a : M) : a^1 = a :=
by rw [pow_succ, pow_zero, mul_one]

/-- Note that most of the lemmas about powers of two refer to it as `sq`. -/
@[to_additive two_nsmul, nolint to_additive_doc]
theorem pow_two (a : M) : a^2 = a * a :=
by rw [pow_succ, pow_one]

alias pow_two ← sq

@[to_additive]
theorem pow_mul_comm' (a : M) (n : ℕ) : a^n * a = a * a^n := commute.pow_self a n

@[to_additive add_nsmul]
theorem pow_add (a : M) (m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n with n ih; [rw [nat.add_zero, pow_zero, mul_one],
  rw [pow_succ', ← mul_assoc, ← ih, ← pow_succ', nat.add_assoc]]

@[simp] lemma pow_boole (P : Prop) [decidable P] (a : M) :
  a ^ (if P then 1 else 0) = if P then a else 1 :=
by simp

-- the attributes are intentionally out of order. `smul_zero` proves `nsmul_zero`.
@[to_additive nsmul_zero, simp] theorem one_pow (n : ℕ) : (1 : M)^n = 1 :=
by induction n with n ih; [exact pow_zero _, rw [pow_succ, ih, one_mul]]

@[to_additive mul_nsmul']
theorem pow_mul (a : M) (m n : ℕ) : a^(m * n) = (a^m)^n :=
begin
  induction n with n ih,
  { rw [nat.mul_zero, pow_zero, pow_zero] },
  { rw [nat.mul_succ, pow_add, pow_succ', ih] }
end

@[to_additive nsmul_left_comm]
lemma pow_right_comm (a : M) (m n : ℕ) : (a^m)^n = (a^n)^m :=
by rw [←pow_mul, nat.mul_comm, pow_mul]

@[to_additive mul_nsmul]
theorem pow_mul' (a : M) (m n : ℕ) : a^(m * n) = (a^n)^m :=
by rw [nat.mul_comm, pow_mul]

@[to_additive nsmul_add_sub_nsmul]
theorem pow_mul_pow_sub (a : M) {m n : ℕ} (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n :=
by rw [←pow_add, nat.add_comm, tsub_add_cancel_of_le h]

@[to_additive sub_nsmul_nsmul_add]
theorem pow_sub_mul_pow (a : M) {m n : ℕ} (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n :=
by rw [←pow_add, tsub_add_cancel_of_le h]

@[to_additive bit0_nsmul]
theorem pow_bit0 (a : M) (n : ℕ) : a ^ bit0 n = a^n * a^n := pow_add _ _ _

@[to_additive bit1_nsmul]
theorem pow_bit1 (a : M) (n : ℕ) : a ^ bit1 n = a^n * a^n * a :=
by rw [bit1, pow_succ', pow_bit0]

@[to_additive]
theorem pow_mul_comm (a : M) (m n : ℕ) : a^m * a^n = a^n * a^m :=
commute.pow_pow_self a m n

@[to_additive]
lemma commute.mul_pow {a b : M} (h : commute a b) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
nat.rec_on n (by simp only [pow_zero, one_mul]) $ λ n ihn,
by simp only [pow_succ, ihn, ← mul_assoc, (h.pow_left n).right_comm]

@[to_additive bit0_nsmul']
theorem pow_bit0' (a : M) (n : ℕ) : a ^ bit0 n = (a * a) ^ n :=
by rw [pow_bit0, (commute.refl a).mul_pow]

@[to_additive bit1_nsmul']
theorem pow_bit1' (a : M) (n : ℕ) : a ^ bit1 n = (a * a) ^ n * a :=
by rw [bit1, pow_succ', pow_bit0']

lemma dvd_pow {x y : M} (hxy : x ∣ y) :
  ∀ {n : ℕ} (hn : n ≠ 0), x ∣ y^n
| 0       hn := (hn rfl).elim
| (n + 1) hn := by { rw pow_succ, exact hxy.mul_right _ }

alias dvd_pow ← has_dvd.dvd.pow

lemma dvd_pow_self (a : M) {n : ℕ} (hn : n ≠ 0) : a ∣ a^n :=
dvd_rfl.pow hn

end monoid

/-!
### Commutative (additive) monoid
-/

section comm_monoid
variables [comm_monoid M] [add_comm_monoid A]

@[to_additive nsmul_add]
theorem mul_pow (a b : M) (n : ℕ) : (a * b)^n = a^n * b^n :=
(commute.all a b).mul_pow n


/-- The `n`th power map on a commutative monoid for a natural `n`, considered as a morphism of
monoids. -/
@[to_additive "Multiplication by a natural `n` on a commutative additive
monoid, considered as a morphism of additive monoids.", simps]
def pow_monoid_hom (n : ℕ) : M →* M :=
{ to_fun := (^ n),
  map_one' := one_pow _,
  map_mul' := λ a b, mul_pow a b n }

-- the below line causes the linter to complain :-/
-- attribute [simps] pow_monoid_hom nsmul_add_monoid_hom

end comm_monoid

section div_inv_monoid
variable [div_inv_monoid G]

open int

@[simp, to_additive one_zsmul]
theorem zpow_one (a : G) : a ^ (1:ℤ) = a :=
by { convert pow_one a using 1, exact zpow_coe_nat a 1 }

@[to_additive two_zsmul]
theorem zpow_two (a : G) : a ^ (2 : ℤ) = a * a :=
by { convert pow_two a using 1, exact zpow_coe_nat a 2 }

@[to_additive neg_one_zsmul]
theorem zpow_neg_one (x : G) : x ^ (-1:ℤ) = x⁻¹ :=
(zpow_neg_succ_of_nat x 0).trans $ congr_arg has_inv.inv (pow_one x)

@[to_additive]
theorem zpow_neg_coe_of_pos (a : G) : ∀ {n : ℕ}, 0 < n → a ^ -(n:ℤ) = (a ^ n)⁻¹
| (n+1) _ := zpow_neg_succ_of_nat _ _

end div_inv_monoid

section division_monoid
variables [division_monoid α] {a b : α}

@[simp, to_additive] lemma inv_pow (a : α) : ∀ n : ℕ, (a⁻¹) ^ n = (a ^ n)⁻¹
| 0       := by rw [pow_zero, pow_zero, inv_one]
| (n + 1) := by rw [pow_succ', pow_succ, inv_pow, mul_inv_rev]

-- the attributes are intentionally out of order. `smul_zero` proves `zsmul_zero`.
@[to_additive zsmul_zero, simp] lemma one_zpow : ∀ (n : ℤ), (1 : α) ^ n = 1
| (n : ℕ) := by rw [zpow_coe_nat, one_pow]
| -[1+ n] := by rw [zpow_neg_succ_of_nat, one_pow, inv_one]

@[simp, to_additive neg_zsmul] lemma zpow_neg (a : α) : ∀ (n : ℤ), a ^ -n = (a ^ n)⁻¹
| (n+1:ℕ) := div_inv_monoid.zpow_neg' _ _
| 0       := by { change a ^ (0 : ℤ) = (a ^ (0 : ℤ))⁻¹, simp }
| -[1+ n] := by { rw [zpow_neg_succ_of_nat, inv_inv, ← zpow_coe_nat], refl }

@[to_additive neg_one_zsmul_add]
lemma mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : ℤ) = b ^ (-1 : ℤ) * a ^ (-1 : ℤ) :=
by simp_rw [zpow_neg_one, mul_inv_rev]

@[to_additive zsmul_neg] lemma inv_zpow (a : α) : ∀ n : ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
| (n : ℕ) := by rw [zpow_coe_nat, zpow_coe_nat, inv_pow]
| -[1+ n] := by rw [zpow_neg_succ_of_nat, zpow_neg_succ_of_nat, inv_pow]

@[simp, to_additive zsmul_neg']
lemma inv_zpow' (a : α) (n : ℤ) : a⁻¹ ^ n = a ^ (-n) := by rw [inv_zpow, zpow_neg]

@[to_additive nsmul_zero_sub]
lemma one_div_pow (a : α) (n : ℕ) : (1 / a) ^ n = 1 / a ^ n := by simp_rw [one_div, inv_pow]

@[to_additive zsmul_zero_sub]
lemma one_div_zpow (a : α) (n : ℤ) :  (1 / a) ^ n = 1 / a ^ n := by simp_rw [one_div, inv_zpow]

@[to_additive add_commute.zsmul_add]
protected lemma commute.mul_zpow (h : commute a b) : ∀ (i : ℤ), (a * b) ^ i = a ^ i * b ^ i
| (n : ℕ) := by simp [h.mul_pow n]
| -[1+n]  := by simp [h.mul_pow, (h.pow_pow _ _).eq, mul_inv_rev]

end division_monoid

section division_comm_monoid
variables [division_comm_monoid α]

@[to_additive zsmul_add] lemma mul_zpow (a b : α) : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n :=
(commute.all a b).mul_zpow

@[simp, to_additive nsmul_sub] lemma div_pow (a b : α) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_pow, inv_pow]

@[simp, to_additive zsmul_sub] lemma div_zpow (a b : α) (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n :=
by simp only [div_eq_mul_inv, mul_zpow, inv_zpow]

/-- The `n`-th power map (for an integer `n`) on a commutative group, considered as a group
homomorphism. -/
@[to_additive "Multiplication by an integer `n` on a commutative additive group, considered as an
additive group homomorphism.", simps]
def zpow_group_hom (n : ℤ) : α →* α :=
{ to_fun := (^ n),
  map_one' := one_zpow n,
  map_mul' := λ a b, mul_zpow a b n }

end division_comm_monoid

section group
variables [group G] [group H] [add_group A] [add_group B]

@[to_additive sub_nsmul] lemma pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a^(m - n) = a^m * (a^n)⁻¹ :=
eq_mul_inv_of_mul_eq $ by rw [←pow_add, tsub_add_cancel_of_le h]

@[to_additive] lemma pow_inv_comm (a : G) (m n : ℕ) : (a⁻¹)^m * a^n = a^n * (a⁻¹)^m :=
(commute.refl a).inv_left.pow_pow _ _

@[to_additive sub_nsmul_neg]
lemma inv_pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a⁻¹^(m - n) = (a^m)⁻¹ * a^n :=
by rw [pow_sub a⁻¹ h, inv_pow, inv_pow, inv_inv]

end group

lemma zero_pow [monoid_with_zero R] : ∀ {n : ℕ}, 0 < n → (0 : R) ^ n = 0
| (n+1) _ := by rw [pow_succ, zero_mul]

lemma zero_pow_eq [monoid_with_zero R] (n : ℕ) : (0 : R)^n = if n = 0 then 1 else 0 :=
begin
  split_ifs with h,
  { rw [h, pow_zero], },
  { rw [zero_pow (nat.pos_of_ne_zero h)] },
end

lemma pow_eq_zero_of_le [monoid_with_zero M] {x : M} {n m : ℕ}
  (hn : n ≤ m) (hx : x^n = 0) : x^m = 0 :=
by rw [← tsub_add_cancel_of_le hn, pow_add, hx, mul_zero]

namespace ring_hom

variables [semiring R] [semiring S]

protected lemma map_pow (f : R →+* S) (a) :
  ∀ n : ℕ, f (a ^ n) = (f a) ^ n :=
map_pow f a

end ring_hom

lemma pow_dvd_pow [monoid R] (a : R) {m n : ℕ} (h : m ≤ n) :
  a ^ m ∣ a ^ n := ⟨a ^ (n - m), by rw [← pow_add, nat.add_comm, tsub_add_cancel_of_le h]⟩

theorem pow_dvd_pow_of_dvd [comm_monoid R] {a b : R} (h : a ∣ b) : ∀ n : ℕ, a ^ n ∣ b ^ n
| 0     := by rw [pow_zero, pow_zero]
| (n+1) := by { rw [pow_succ, pow_succ], exact mul_dvd_mul h (pow_dvd_pow_of_dvd n) }

theorem pow_eq_zero [monoid_with_zero R] [no_zero_divisors R] {x : R} {n : ℕ} (H : x^n = 0) :
  x = 0 :=
begin
  induction n with n ih,
  { rw pow_zero at H,
    rw [← mul_one x, H, mul_zero] },
  { rw pow_succ at H,
    exact or.cases_on (mul_eq_zero.1 H) id ih }
end

@[simp] lemma pow_eq_zero_iff [monoid_with_zero R] [no_zero_divisors R]
  {a : R} {n : ℕ} (hn : 0 < n) :
  a ^ n = 0 ↔ a = 0 :=
begin
  refine ⟨pow_eq_zero, _⟩,
  rintros rfl,
  exact zero_pow hn,
end

lemma pow_ne_zero_iff [monoid_with_zero R] [no_zero_divisors R] {a : R} {n : ℕ} (hn : 0 < n) :
  a ^ n ≠ 0 ↔ a ≠ 0 :=
(pow_eq_zero_iff hn).not

@[field_simps] theorem pow_ne_zero [monoid_with_zero R] [no_zero_divisors R]
  {a : R} (n : ℕ) (h : a ≠ 0) : a ^ n ≠ 0 :=
mt pow_eq_zero h

theorem sq_eq_zero_iff [monoid_with_zero R] [no_zero_divisors R] {a : R} : a ^ 2 = 0 ↔ a = 0 :=
pow_eq_zero_iff two_pos

lemma pow_dvd_pow_iff [cancel_comm_monoid_with_zero R]
  {x : R} {n m : ℕ} (h0 : x ≠ 0) (h1 : ¬ is_unit x) :
  x ^ n ∣ x ^ m ↔ n ≤ m :=
begin
  split,
  { intro h, rw [← not_lt], intro hmn, apply h1,
    have : x ^ m * x ∣ x ^ m * 1,
    { rw [← pow_succ', mul_one], exact (pow_dvd_pow _ (nat.succ_le_of_lt hmn)).trans h },
    rwa [mul_dvd_mul_iff_left, ← is_unit_iff_dvd_one] at this, apply pow_ne_zero m h0 },
  { apply pow_dvd_pow }
end

section semiring
variables [semiring R]

lemma min_pow_dvd_add {n m : ℕ} {a b c : R} (ha : c ^ n ∣ a) (hb : c ^ m ∣ b) :
  c ^ (min n m) ∣ a + b :=
begin
  replace ha := (pow_dvd_pow c (min_le_left n m)).trans ha,
  replace hb := (pow_dvd_pow c (min_le_right n m)).trans hb,
  exact dvd_add ha hb
end

end semiring

section comm_semiring
variables [comm_semiring R]

lemma add_sq (a b : R) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
by simp only [sq, add_mul_self_eq]

lemma add_sq' (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b :=
by rw [add_sq, add_assoc, add_comm _ (b ^ 2), add_assoc]

alias add_sq ← add_pow_two

end comm_semiring

section has_distrib_neg
variables [monoid R] [has_distrib_neg R]

variables (R)
theorem neg_one_pow_eq_or : ∀ n : ℕ, (-1 : R)^n = 1 ∨ (-1 : R)^n = -1
| 0     := or.inl (pow_zero _)
| (n+1) := (neg_one_pow_eq_or n).swap.imp
  (λ h, by rw [pow_succ, h, neg_one_mul, neg_neg])
  (λ h, by rw [pow_succ, h, mul_one])
variables {R}

theorem neg_pow (a : R) (n : ℕ) : (- a) ^ n = (-1) ^ n * a ^ n :=
(neg_one_mul a) ▸ (commute.neg_one_left a).mul_pow n

@[simp] theorem neg_pow_bit0 (a : R) (n : ℕ) : (- a) ^ (bit0 n) = a ^ (bit0 n) :=
by rw [pow_bit0', neg_mul_neg, pow_bit0']

@[simp] theorem neg_pow_bit1 (a : R) (n : ℕ) : (- a) ^ (bit1 n) = - a ^ (bit1 n) :=
by simp only [bit1, pow_succ, neg_pow_bit0, neg_mul_eq_neg_mul]

@[simp] lemma neg_sq (a : R) : (-a) ^ 2 = a ^ 2 := by simp [sq]
@[simp] lemma neg_one_sq : (-1 : R) ^ 2 = 1 := by rw [neg_sq, one_pow]

alias neg_sq ← neg_pow_two
alias neg_one_sq ← neg_one_pow_two

end has_distrib_neg

section ring
variables [ring R] {a b : R}

protected lemma commute.sq_sub_sq (h : commute a b) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by rw [sq, sq, h.mul_self_sub_mul_self_eq]

@[simp]
lemma neg_one_pow_mul_eq_zero_iff {n : ℕ} {r : R} : (-1)^n * r = 0 ↔ r = 0 :=
by rcases neg_one_pow_eq_or R n; simp [h]

@[simp]
lemma mul_neg_one_pow_eq_zero_iff {n : ℕ} {r : R} : r * (-1)^n = 0 ↔ r = 0 :=
by rcases neg_one_pow_eq_or R n; simp [h]

variables [no_zero_divisors R]

protected lemma commute.sq_eq_sq_iff_eq_or_eq_neg (h : commute a b) :
  a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
by rw [←sub_eq_zero, h.sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_comm]

@[simp] lemma sq_eq_one_iff : a^2 = 1 ↔ a = 1 ∨ a = -1 :=
by rw [←(commute.one_right a).sq_eq_sq_iff_eq_or_eq_neg, one_pow]

lemma sq_ne_one_iff : a^2 ≠ 1 ↔ a ≠ 1 ∧ a ≠ -1 := sq_eq_one_iff.not.trans not_or_distrib

end ring

section comm_ring
variables [comm_ring R]

lemma sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := (commute.all a b).sq_sub_sq

alias sq_sub_sq ← pow_two_sub_pow_two

lemma sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 :=
by rw [sub_eq_add_neg, add_sq, neg_sq, mul_neg, ← sub_eq_add_neg]

alias sub_sq ← sub_pow_two

lemma sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b :=
by rw [sub_eq_add_neg, add_sq', neg_sq, mul_neg, ← sub_eq_add_neg]

variables [no_zero_divisors R] {a b : R}

lemma sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
(commute.all a b).sq_eq_sq_iff_eq_or_eq_neg

lemma eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b ^ 2 → a = b ∨ a = -b :=
sq_eq_sq_iff_eq_or_eq_neg.1

/- Copies of the above comm_ring lemmas for `units R`. -/
namespace units

protected lemma sq_eq_sq_iff_eq_or_eq_neg {a b : Rˣ} : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
by simp_rw [ext_iff, coe_pow, sq_eq_sq_iff_eq_or_eq_neg, units.coe_neg]

protected lemma eq_or_eq_neg_of_sq_eq_sq (a b : Rˣ) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b :=
units.sq_eq_sq_iff_eq_or_eq_neg.1 h

end units

end comm_ring

lemma of_add_nsmul [add_monoid A] (x : A) (n : ℕ) :
  multiplicative.of_add (n • x) = (multiplicative.of_add x)^n := rfl

lemma of_add_zsmul [sub_neg_monoid A] (x : A) (n : ℤ) :
  multiplicative.of_add (n • x) = (multiplicative.of_add x)^n := rfl

lemma of_mul_pow [monoid A] (x : A) (n : ℕ) :
  additive.of_mul (x ^ n) = n • (additive.of_mul x) := rfl

lemma of_mul_zpow [div_inv_monoid G] (x : G) (n : ℤ) :
  additive.of_mul (x ^ n) = n • additive.of_mul x :=
rfl

@[simp, to_additive]
lemma semiconj_by.zpow_right [group G] {a x y : G} (h : semiconj_by a x y) :
  ∀ m : ℤ, semiconj_by a (x^m) (y^m)
| (n : ℕ) := by simp [zpow_coe_nat, h.pow_right n]
| -[1+n] := by simp [(h.pow_right n.succ).inv_right]

namespace commute

variables [group G] {a b : G}

@[simp, to_additive] lemma zpow_right (h : commute a b) (m : ℤ) : commute a (b^m) := h.zpow_right m

@[simp, to_additive] lemma zpow_left (h : commute a b) (m : ℤ) : commute (a^m) b :=
(h.symm.zpow_right m).symm

@[to_additive]
lemma zpow_zpow (h : commute a b) (m n : ℤ) : commute (a^m) (b^n) := (h.zpow_left m).zpow_right n

variables (a) (m n : ℤ)

@[simp, to_additive] lemma self_zpow : commute a (a ^ n) := (commute.refl a).zpow_right n
@[simp, to_additive] lemma zpow_self : commute (a ^ n) a := (commute.refl a).zpow_left n
@[simp, to_additive] lemma zpow_zpow_self : commute (a ^ m) (a ^ n) :=
(commute.refl a).zpow_zpow m n

end commute
