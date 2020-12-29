/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard
-/
import data.rat
import data.fintype.card
import data.nat.choose.binomial
import algebra.big_operators.nat_antidiagonal
import ring_theory.power_series.well_known

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, 1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the formula for the the sum
of the first $n$ `k`th powers, they are related to the Taylor series of
certain trigonometric and hyperbolic functions, and also show up in the values
that the Riemann Zeta function takes both at both negative and positive integers.
For example If $1 \leq n$ is even then

$$\zeta(2n)=\sum_{t\geq1}t^{-2n}=(-1)^{n+1}\frac{(2\pi)^{2n}B_{2n}}{2(2n)!}.$$

Note however that many of these results are not yet formalised in Lean.

The Bernoulli numbers can be formally defined using the power series

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

-- TODO : do we have this?

although that happens to not be the definition in mathlib (this is an *implementation
detail* though, and need not concern the mathematician).

## Implementation detail

```
def bernoulli : ℕ → ℚ :=
well_founded.fix nat.lt_wf
  (λ n bernoulli, 1 - ∑ k : fin n, (n.choose k) * bernoulli k k.2 / (n + 1 - k))
```
The formal definition has the property that `bernoulli 0 = 1`

-- Should use finset, not fin?

--
According to Wikipedia https://en.wikipedia.org/wiki/Bernoulli_number there are
two conventions for Bernoulli numbers. Lean's `bernoulli (n : ℕ) : ℚ` is the
convention denoted $$B_n^+$$ on Wikipedia.  `n`'th
Bernoulli number.


In this file, we provide the definition,
and the basic fact (`sum_bernoulli`) that
$$ \sum_{k < n} \binom{n}{k} * B_k = n, $$
where $B_k$ denotes the the $k$-th Bernoulli number.

-/

open_locale big_operators

/-- The Bernoulli numbers:
the $n$-th Bernoulli number $B_n$ is defined recursively via
$$B_n = 1 - \sum_{k < n} \binom{n}{k}\frac{B_k}{n+1-k}$$ -/
def bernoulli : ℕ → ℚ :=
well_founded.fix nat.lt_wf
  (λ n bernoulli, 1 - ∑ k : fin n, n.choose k / (n - k + 1) * bernoulli k k.2)

lemma bernoulli_def' (n : ℕ) :
  bernoulli n = 1 - ∑ k : fin n, n.choose k / (n - k + 1) * bernoulli k :=
well_founded.fix_eq _ _ _

lemma bernoulli_def (n : ℕ) :
  bernoulli n = 1 - ∑ k in finset.range n, n.choose k / (n - k + 1) * bernoulli k :=
by { rw [bernoulli_def', ← fin.sum_univ_eq_sum_range], refl }

lemma bernoulli_spec (n : ℕ) :
  ∑ k in finset.range n.succ, (n.choose k : ℚ) / (n - k + 1) * bernoulli k = 1 :=
by simp [finset.sum_range_succ, bernoulli_def n]

-- branch mem_range_succ_iff -- did it compile or shall I unsimp?
#check finset.mem_range
@[simp] lemma finset.mem_range_succ_iff {a b : ℕ} : a ∈ finset.range b.succ ↔ a ≤ b :=
by simp only [nat.lt_succ_iff, finset.mem_range]

open finset

-- move out of this PR

lemma sum_range_succ_eq_sum_antidiagonal {M : Type*} [add_comm_monoid M] (f : ℕ → ℕ → M) (n : ℕ) :
  ∑ ij in finset.nat.antidiagonal n, f ij.1 ij.2 = ∑ k in range n.succ, f k (n - k) :=
begin
  symmetry,
  refine finset.sum_bij'
  (λ a _, (a, n - a) : Π (a : ℕ), a ∈ finset.range n.succ → ℕ × ℕ)
  _ (by simp)
  (λ (ij : ℕ × ℕ) _, ij.1)
  _ (by simp) _,
  { intros a ha, simp [nat.add_sub_cancel' (mem_range_succ_iff.1 ha)], },
  { intros _ ha, simp [nat.le.intro (nat.mem_antidiagonal.1 ha)] },
  { rintro ⟨i, j⟩ ha, ext, refl, rw ← (nat.mem_antidiagonal.1 ha), exact nat.add_sub_cancel_left _ _ },
end

-- hopefully don't need

-- lemma this_is_so_stupid (n : ℕ) :
-- ∑ (k : ℕ) in range n.succ, (k.binomial (n - k) : ℚ) / (n - k + 1) * bernoulli k
-- =
-- ∑ (k : ℕ) in range n.succ, k.binomial (n - k) / ((n - k : ℕ) + 1) * bernoulli k
-- :=
-- begin
--   apply finset.sum_congr rfl,
--   intros k hk,
-- -- next line was written with
-- --  congr', symmetry, apply nat.cast_sub, library_search,
--   rw nat.cast_sub (finset.mem_range_succ_iff.mp hk),
-- end

lemma bernoulli_spec' (n : ℕ) :
  ∑ k in finset.nat.antidiagonal n,
  ((k.1 + k.2).choose k.2 : ℚ) / (k.2 + 1) * bernoulli k.1 = 1 :=
begin
  convert bernoulli_spec n using 1,
  symmetry,
  rw sum_range_succ_eq_sum_antidiagonal (λ i j, ((i + j).choose j : ℚ) / (j + 1) * bernoulli i) n,
  apply finset.sum_congr rfl,
  intros k hk, rw mem_range_succ_iff at hk,
  congr' 3,
  { rw ← nat.choose_symm_add, congr', exact (nat.add_sub_of_le hk).symm },
  { norm_cast }
end

open_locale nat

lemma what_am_i_doing_wrong (n : ℕ) :
  ∑ (k : ℕ) in range n.succ, ↑(k.binomial (n.succ - k)) * bernoulli k =
  ∑ (k : ℕ) in range n.succ, ↑(k.binomial (n - k).succ) * bernoulli k :=
begin
  apply finset.sum_congr rfl, -- gives us assumption k ≤ n
  intros k hk,
  rw nat.succ_sub (finset.mem_range_succ_iff.mp hk),
end

open nat

@[simp] lemma sum_bernoulli' (n : ℕ) :
  ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli k = n :=
begin
  -- n = 0 is a special case so let's prove it for n of the form d + 1.
  cases n with d, simp, -- checking special case n = 0 with `simp`
  -- n = d + 1 case: By definition of B_d, goal obviously equivalent to
  -- $$\Sum_{k\leq d}\binom{d+1}k\cdot B_k=\Sum_{k\leq d}(d+1)\binom{d}{x}\frac{B_k}{d+1-k}$$
  rw [← mul_one (d.succ : ℚ), ← bernoulli_spec' d, finset.mul_sum],
  -- change other sum to antidiag
  -- rw what_am_i_doing_wrong,
  rw sum_range_succ_eq_sum_antidiagonal
  (λ i j, (d.succ : ℚ) * ( (i+j).choose j / (j + 1) * bernoulli i)) d,
  apply finset.sum_congr rfl,
  rintro k hk, rw mem_range_succ_iff at hk, dsimp only,
  -- eliminate bernoulli,
  rw ← mul_assoc, congr',
  -- clear denoms
  have h : ((d - k : ℕ) : ℚ) + 1 ≠ 0,
  { norm_cast, simp },
  field_simp [h],
  -- down to nat
  norm_cast,
  -- introduce i and prove i + k = d
  set i := d - k with hi,
  rw ← choose_symm (le_trans hk (le_succ d)),
  have hi3 : k + i = d := add_sub_of_le hk,
  rw [← hi3, succ_mul_choose_eq],
  congr', exact norm_num.sub_nat_pos (k + i).succ k (succ i) rfl,
end

-- Is this the way to say it?
-- the "missing term" (n+1).binomial 0 * bernoulli (n+1) is B_{n+1}
@[simp] lemma sum_bernoulli_antidiag (n : ℕ) :
  (∑ ij in finset.nat.antidiagonal n,
   ((ij.1 + ij.2).succ.choose ij.1 : ℚ) * bernoulli ij.1) = n.succ :=
begin
  rw sum_range_succ_eq_sum_antidiagonal (λ (i j : ℕ) , ((i + j).succ.choose i : ℚ) * bernoulli i),
  dsimp,
  convert sum_bernoulli' n.succ using 1,
  apply finset.sum_congr rfl,
  intros k hk, rw mem_range_succ_iff at hk,
  -- remove bernoulli
  congr',
  exact add_sub_of_le hk,
end


/-

# Examples

-/


@[simp] lemma bernoulli_zero  : bernoulli 0 = 1   := rfl

-- a rival `bernoulli_neg` convention has this as -1/2 and all other ones the same

@[simp] lemma bernoulli_one   : bernoulli 1 = 1/2 :=
begin
  rw [bernoulli_def, sum_range_one], norm_num
end
@[simp] lemma bernoulli_two   : bernoulli 2 = 1/6 :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_one], norm_num
end
@[simp] lemma bernoulli_three : bernoulli 3 = 0   :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_succ, sum_range_one], norm_num,
end
@[simp] lemma bernoulli_four  : bernoulli 4 = -1/30 :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_one],
  rw (show nat.choose 4 2 = 6, from dec_trivial), -- shrug
  norm_num,
end

-- experiments

--$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

open power_series

@[simp] lemma constant_coeff_exp : constant_coeff ℚ (exp ℚ) = 1 := rfl

lemma algebra_map_rat_subsingleton (R : Type*) [semiring R] [algebra ℚ R] : subsingleton (ℚ →+* R) :=
by apply_instance

def f : ℚ →+* ℚ := by refine_struct { to_fun := id}; tidy

theorem thing (q : ℚ) : algebra_map ℚ ℚ q = q :=
begin
  rw show algebra_map ℚ ℚ = f, by simp,
  refl,
end

def choose_eq_factorial_div_factorial' {a b : ℕ}
  (hab : a ≤ b) : (b.choose a : ℚ) = b! / (a! * (b - a)!) :=
begin
  field_simp [mul_ne_zero, factorial_ne_zero],
  norm_cast,
  rw ← choose_mul_factorial_mul_factorial hab,
  ring,
end

#check choose_mul_factorial_mul_factorial

lemma choose_spec {i j : ℕ} : i! * j! * (i + j).choose j = (i + j)! :=
begin
  rw ← choose_mul_factorial_mul_factorial (show j ≤ i + j, by simp),
  simp, ring,
end


theorem bernoulli_power_series :
(power_series.mk (λ n, bernoulli n / n!) : power_series ℚ) * (power_series.exp ℚ - 1) =
  (X : power_series ℚ) * exp ℚ :=
begin
  ext n,
  -- constant coefficient is a special case
  cases n, simp only [ring_hom.map_sub, constant_coeff_one, zero_mul, constant_coeff_exp, constant_coeff_X, coeff_zero_eq_constant_coeff,
  mul_zero, sub_self, ring_hom.map_mul],
  rw coeff_mul,
  rw mul_comm X,
  rw coeff_succ_mul_X,
  simp only [coeff_mk, coeff_one, coeff_exp, linear_map.map_sub, factorial, thing],
  rw nat.sum_antidiagonal_succ',
  simp, --squeeze_simp hangs
  apply eq_inv_of_mul_left_eq_one,
  rw sum_mul,
  convert bernoulli_spec' n using 1,
  apply sum_congr rfl,
  rintro ⟨i, j⟩ hn, rw nat.mem_antidiagonal at hn, subst hn, dsimp only,
  have hj : (j : ℚ) + 1 ≠ 0, by norm_cast; linarith,
  have hj' : j.succ ≠ 0, by {show j + 1 ≠ 0, by linarith},
  have haargh : ((j : ℚ) + 1) * j! * i! ≠ 0 := by norm_cast; exact
    mul_ne_zero (mul_ne_zero hj' (factorial_ne_zero j)) (factorial_ne_zero _),
  field_simp [hj, haargh],
  norm_cast,
  rw [mul_comm _ (bernoulli i), mul_assoc, mul_assoc],
  apply congr_arg,
  norm_cast,
  rw ← _root_.choose_spec,
  ring,
end
