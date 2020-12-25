/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard
-/
import data.rat
import data.fintype.card
import data.nat.choose.binomial
import algebra.big_operators.nat_antidiagonal

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, 1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the Taylor series of trigonometric
and hyperbolic functions, and they are related to the values that the Riemann Zeta function
takes at negative integers. If $2 \leq k$ is even then

$$\sum_{n\geq1}n^{-k}=B_k\pi^k.$$


relate  multiples of products of powers of `π` and)
special values of the Riemann zeta function, although many of these things are not
yet formalised.

The Bernoulli numbers can be formally defined thus:

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* though, and need not concern the mathematician).

-- TODO : prove the displayed equation above

Note: Not all of these facts are available in mathlib.

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

For example, they show up in the Taylor series of many trigonometric and hyperbolic functions,
and also as (integral multiples of products of powers of `π` and)
special values of the Riemann zeta function.
(Note: these facts are not yet available in mathlib)

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
  (λ n bernoulli, 1 - ∑ k : fin n, (k : ℕ).binomial (n - k) / (n - k + 1) * bernoulli k k.2)

lemma bernoulli_def' (n : ℕ) :
  bernoulli n = 1 - ∑ k : fin n, (k : ℕ).binomial (n - k) / (n - k + 1) * bernoulli k :=
well_founded.fix_eq _ _ _

lemma bernoulli_def (n : ℕ) :
  bernoulli n = 1 - ∑ k in finset.range n, (k : ℕ).binomial (n - k) / (n - k + 1) * bernoulli k :=
by { rw [bernoulli_def', ← fin.sum_univ_eq_sum_range], refl }

lemma bernoulli_spec (n : ℕ) :
  ∑ k in finset.range n.succ, (k.binomial (n - k) : ℚ) / (n - k + 1) * bernoulli k = 1 :=
by simp [finset.sum_range_succ, bernoulli_def n]

/-
finset.sum_bij' :
  ∀ {X M Y : Type} [add_comm_monoid M]
    {s : finset X} {t : finset Y}
    {f : X → M} {g : Y → M}
    (i : Π (a ∈ s) → γ)
      (hi : ∀ (a ∈ s), i a ha ∈ t)
      (h37 : ∀ (a ∈ s), f a = g (i a ha))
    (j : Π (a ∈ t) → α)
     (hj : ∀ (a ∈ t), j a ha ∈ s),
     (∀ (a : α) (ha : a ∈ s), j (i a ha) _ = a) →
     (∀ (a : γ) (ha : a ∈ t), i (j a ha) _ = a) →
     ∑ (x : α) in s, f x = ∑ (x : γ) in t, g x
-/
lemma bernoulli_spec' (n : ℕ) :
  ∑ k in finset.nat.antidiagonal n,
  (k.1.binomial k.2 : ℚ) / (k.2 + 1) * bernoulli k.1 = 1 :=
begin
  conv_rhs {rw ← bernoulli_spec n},
  apply finset.sum_bij' (λ (ij : ℕ × ℕ) _, ij.1),
  dsimp, sorry end #exit
  refine @@finset.sum_bij' _ (λ ij, i.1) (λ (k : ℕ), (k.binomial (n - k) : ℚ) / (n - k + 1) * bernoulli k) (begin sorry end) _ _ _ _ _ _,
  repeat {sorry},
end
#exit

   (λ (i ∈ finset.nat.antidiagonal n), i.1)
  (by {
    -- next line makes goal insolvable
    -- rintro ⟨i, j⟩ h, simp [h, nat.lt_succ_iff, nat.le.intro] at *, sorry})
    rintro ⟨i, j⟩ h, have : i + j = n, simpa using h,
     simp [nat.lt_succ_iff, nat.le.intro this] } )
  _
  (λ k _, (k, n - k))
  _ _ _,
  { begin
    rintros ⟨i, j⟩ h,
    simp only [finset.nat.mem_antidiagonal] at h,
    subst h,
    dsimp,
    simp [-finset.sum_range_succ],
    squeeze_simp,

    sorry
  end}, -- looks messy?
  { -- annoying
    by {simp, omega}},
  { by {simp, omega}},
  { by {simp }},
end

#print finset.prod_bij
#print finset.sum_bij

@[simp] lemma bernoulli_zero  : bernoulli 0 = 1   := rfl
@[simp] lemma bernoulli_one   : bernoulli 1 = 1/2 :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end
@[simp] lemma bernoulli_two   : bernoulli 2 = 1/6 :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end
@[simp] lemma bernoulli_three : bernoulli 3 = 0   :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end
@[simp] lemma bernoulli_four  : bernoulli 4 = -1/30 :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end

open_locale nat

theorem nat.binomial_spec' {a b : ℕ} : (a.binomial b : ℚ) = (a + b)! / (a! * b!) :=
begin
  symmetry,
  rw [div_eq_iff, mul_comm],
  { norm_cast,
    rw nat.binomial_spec },
  norm_cast,
  apply mul_ne_zero;
  apply nat.factorial_ne_zero,
end

open nat

@[simp] lemma sum_bernoulli' (n : ℕ) :
  ∑ k in finset.range n, (k.binomial (n - k) : ℚ) * bernoulli k = n :=
begin
  -- n = 0 is a special case so let's prove it for n of the form d + 1.
  cases n with d, simp, -- checking special case n = 0 with `simp`
  -- n = d + 1 case: By definition of B_d, goal obviously equivalent to
  -- $$\Sum_{k\leq d}\binom{d+1}k\cdot B_k=\Sum_{k\leq d}(d+1)\binom{d}{x}\frac{B_k}{d+1-k}$$
  rw [← mul_one (d.succ : ℚ), ← bernoulli_spec d, finset.mul_sum],
  -- It suffices to show the summands are equal pairwise
  apply finset.sum_congr rfl,
  -- So assume k <= d are naturals and all we've got to show is
  -- $$\binom{d+1}k=\frac{d+1}{d+1-k}\binom{d}{k}$$.
  -- We do this by rewriting eveything in terms of factorials,
  -- because it seems less painless than casting everything to nat (I tried).
  -- Let's start from he beginning. Let `k ≤ d` be naturals.
  intros k hkd_nat, rw [finset.mem_range, nat.lt_succ_iff] at hkd_nat, -- now in a ghandy form.
  -- But do I ever use it?
  -- now
  -- cancel bernoullis,
  rw ← mul_assoc, congr',
  -- now factorial definition of `binomial`
  simp [binomial_spec', succ_eq_add_one],
  -- the block is now k + (d - k), which is d by hkd_nat
  have hmagic : k + (d - k) = d := nat.add_sub_cancel' hkd_nat,
  rw hmagic,
  -- now it all comes out really nicely.
  -- except the next 7 lines should just be `field_simp` or maybe some specialised "clear denominator" tactic.
  have hfactorials_arent_zero_and_products_arent_zero1 : (k! : ℚ) * ↑(d + 1 - k)! ≠ 0,
  { apply mul_ne_zero;
    norm_cast;
    apply factorial_ne_zero },
  have hlinarith_mod_cast_can_do_me : (d : ℚ)- k + 1 ≠ 0 := by linarith [(show (k : ℚ) ≤ d, by assumption_mod_cast)],
  have hfactorials_arent_zero_and_products_arent_zero2 : (k! : ℚ) * ↑(d - k)! * (↑d - ↑k + 1) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_cast; exact factorial_ne_zero _) (by norm_cast; exact factorial_ne_zero _)) hlinarith_mod_cast_can_do_me,--
  field_simp [hfactorials_arent_zero_and_products_arent_zero1, hfactorials_arent_zero_and_products_arent_zero2],
  --have hcoe_can_do_me : (k : ℚ) ≤ d := by assumption_mod_cast,
  -- Now we can use linarith to ensure all our denominators are nonzero
  -- Next clear denominators. Lean seems to help even though linarith closes all the
  -- obvious goals.
  -- why doesn't field_simp try linarith?
  -- Turns out that we need to change (d + 1) - k to (d - k) + 1 in nat world
  -- this is an annoying technical issue that probably `omega` should be solving,
--  rw [nat.succ_sub hkd_nat, factorial_succ, succ_eq_add_one], push_cast [hkd_nat],
  norm_cast, -- now a question over nat! -- we have good tactics over nat.
  simp only [← succ_eq_add_one, factorial_succ, succ_sub hkd_nat, hmagic],
  ring,
end

@[simp] lemma sum_bernoulli'' (n : ℕ) :
  ∑ k in finset.range n, (k.binomial (n - k) : ℚ) * bernoulli k = n :=
begin
  -- n = 0 is a special case so let's prove it for n of the form d + 1.
  cases n with d, simp, -- checking special case n = 0 with `simp`
  -- n = d + 1 case: By definition of B_d, goal obviously equivalent to
  -- $$\Sum_{k\leq d}\binom{d+1}k\cdot B_k=\Sum_{k\leq d}(d+1)\binom{d}{x}\frac{B_k}{d+1-k}$$
  rw [← mul_one (d.succ : ℚ), ← bernoulli_spec d, finset.mul_sum],
  -- It suffices to show the summands are equal pairwise
  apply finset.sum_congr rfl,
  -- So assume k <= d are naturals and all we've got to show is
  -- $$\binom{d+1}k=\frac{d+1}{d+1-k}\binom{d}{k}$$.
  -- We do this by rewriting eveything in terms of factorials,
  -- because it seems less painless than casting everything to nat (I tried).
  -- Let's start from he beginning. Let `k ≤ d` be naturals.
  intros k hkd_nat, rw [finset.mem_range, nat.lt_succ_iff] at hkd_nat, -- now in a ghandy form.
  -- But do I ever use it?
  -- now
  -- cancel bernoullis,
  rw ← mul_assoc, congr',
  -- now factorial definition of `binomial`
  simp [binomial_spec', succ_eq_add_one],
  -- the block is now k + (d - k), which is d by hkd_nat
  have hmagic : k + (d - k) = d := nat.add_sub_cancel' hkd_nat,
  rw hmagic,
  -- now it all comes out really nicely.
  -- except the next 7 lines should just be `field_simp` or maybe some specialised "clear denominator" tactic.
  have hfactorials_arent_zero_and_products_arent_zero1 : (k! : ℚ) * ↑(d + 1 - k)! ≠ 0,
  { apply mul_ne_zero;
    norm_cast;
    apply factorial_ne_zero },
  have hlinarith_mod_cast_can_do_me : (d : ℚ)- k + 1 ≠ 0 := by linarith [(show (k : ℚ) ≤ d, by assumption_mod_cast)],
  have hfactorials_arent_zero_and_products_arent_zero2 : (k! : ℚ) * ↑(d - k)! * (↑d - ↑k + 1) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_cast; exact factorial_ne_zero _) (by norm_cast; exact factorial_ne_zero _)) hlinarith_mod_cast_can_do_me,--
  field_simp [hfactorials_arent_zero_and_products_arent_zero1, hfactorials_arent_zero_and_products_arent_zero2],
  --have hcoe_can_do_me : (k : ℚ) ≤ d := by assumption_mod_cast,
  -- Now we can use linarith to ensure all our denominators are nonzero
  -- Next clear denominators. Lean seems to help even though linarith closes all the
  -- obvious goals.
  -- why doesn't field_simp try linarith?
  -- Turns out that we need to change (d + 1) - k to (d - k) + 1 in nat world
  -- this is an annoying technical issue that probably `omega` should be solving,
--  rw [nat.succ_sub hkd_nat, factorial_succ, succ_eq_add_one], push_cast [hkd_nat],
  norm_cast, -- now a question over nat! -- we have good tactics over nat.
  simp only [← succ_eq_add_one, factorial_succ, succ_sub hkd_nat, hmagic],
  ring,
end
