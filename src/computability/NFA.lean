/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import data.fintype.basic
import computability.DFA

/-!
# Nondeterministic Finite Automata
This file contains the definition of a Nondeterministic Finite Automaton (NFA), a state machine
which determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular
set by evaluating the string over every possible path.
We show that DFA's are equivalent to NFA's however the construction from NFA to DFA uses an
exponential number of states.
Note that this definition allows for Automaton with infinite states, a `fintype` instance must be
supplied for true NFA's.
-/

universes u v

/-- An NFA is a set of states (`state`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `finset` of states. These are the states that it
  may be sent to. -/
structure NFA (α : Type u) (σ : Type v) :=
(step : σ → α → finset σ)
(start : finset σ)
(accept : finset σ)

variables {α : Type u} {σ σ' σ₁ σ₂ σ₃ : Type v} (M : NFA α σ)
variables [decidable_eq σ] [decidable_eq σ₁] [decidable_eq σ₂] [decidable_eq σ₃]

namespace NFA

instance : inhabited (NFA α σ') := ⟨ NFA.mk (λ _ _, ∅) ∅ ∅ ⟩

/-- `M.step_set S a` is the union of `M.step s a` for all `s ∈ S`. -/
def step_set : finset σ → α → finset σ :=
λ Ss a, finset.bind Ss (λ S, (M.step S a))

lemma mem_step_set (s : σ) (S : finset σ) (a : α) :
  s ∈ M.step_set S a ↔ ∃ t ∈ S, s ∈ M.step t a :=
by rw [step_set, finset.mem_bind]

/-- `M.eval_from S x` computes all possible paths though `M` with input `x` starting at an element
  of `S`. -/
def eval_from (start : finset σ) : list α → finset σ :=
list.foldl M.step_set start

/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start`. -/
def eval := M.eval_from M.start

/-- `M.accepts x` says that there is an accept state in `M.eval x`. -/
def accepts (s : list α) : Prop :=
∃ S ∈ M.accept, S ∈ M.eval s

/-- Two NFA's are equivalent if they accept exactly the same strings. -/
def equiv (M : NFA α σ₁) (N : NFA α σ₂) : Prop := ∀ x, M.accepts x ↔ N.accepts x

local infix ` ≈ ` := equiv

@[refl] lemma equiv_refl (M : NFA α σ) : M ≈ M := λ x, by refl
@[symm] lemma equiv_symm (M : NFA α σ₁) (N : NFA α σ₂) : M ≈ N → N ≈ M := λ h x, (h x).symm
@[trans] lemma equiv_trans (M : NFA α σ₁) (N : NFA α σ₂) (P : NFA α σ₃) : M ≈ N → N ≈ P → M ≈ P :=
λ h₁ h₂ x, iff.trans (h₁ x) (h₂ x)

instance : setoid (Σ σ [decidable_eq σ], NFA α σ) :=
⟨ λ M N, @equiv _ _ _ M.2.1 N.2.1 M.2.2 N.2.2,
  λ M, @equiv_refl _ _ M.2.1 M.2.2,
  λ M N, @equiv_symm _ _ _ M.2.1 N.2.1 M.2.2 N.2.2,
  λ M N P, @equiv_trans _ _ _ _ M.2.1 N.2.1 P.2.1 M.2.2 N.2.2 P.2.2 ⟩

instance : has_coe (DFA α σ') (Σ σ, DFA α σ) := ⟨λ M, ⟨σ', M⟩⟩

@[simp] lemma equiv_def (M : NFA α σ₁) (N : NFA α σ₂) : M ≈ N ↔ ∀ x, M.accepts x ↔ N.accepts x :=
by refl

/-- `M.to_DFA` is an `DFA` constructed from a `NFA` `M` using the subset construction. The
  states is the type of `finset`s of `M.state` and the step function is `M.step_set`. -/
def to_DFA [fintype σ] : DFA α (finset σ) :=
{ step := M.step_set,
  start := M.start,
  accept := finset.univ.filter (λ S, ∃ s ∈ S, s ∈ M.accept) }

lemma to_DFA_correct [fintype σ] (x : list α) :
  M.accepts x ↔ M.to_DFA.accepts x :=
begin
  rw [accepts, DFA.accepts, eval, DFA.eval],
  change _ ↔ list.foldl _ _ _ ∈ finset.univ.filter _,
  rw finset.mem_filter,
  finish
end

end NFA

namespace DFA

/-- `M.to_NFA` is an `NFA` constructed from a `DFA` `M` by using the same start and accept
  states and a transition function which sends `s` with input `a` to the singleton `M.step s a`. -/
def to_NFA (M : DFA α σ') : NFA α σ' :=
{ step := λ s a, {M.step s a},
  start := {M.start},
  accept := M.accept }

@[simp] lemma to_NFA_eval_from_match (M : DFA α σ) (start : σ) (s : list α) :
  M.to_NFA.eval_from {start} s = {M.eval_from start s} :=
begin
  change list.foldl M.to_NFA.step_set {start} s = {list.foldl M.step start s},
  induction s with a s ih generalizing start,
  { tauto },
  { rw [list.foldl, list.foldl],
    have h : M.to_NFA.step_set {start} a = {M.step start a},
    { rw NFA.step_set,
      finish },
    rw h,
    tauto }
end

lemma to_NFA_correct (M : DFA α σ) (x : list α) :
  M.accepts x ↔ M.to_NFA.accepts x :=
begin
  change _ ↔ ∃ S H, S ∈ M.to_NFA.eval_from {M.start} x,
  rw to_NFA_eval_from_match,
  split,
  { intro h,
    use M.eval x,
    finish },
  { rintro ⟨ S, hS₁, hS₂ ⟩,
    rw finset.mem_singleton at hS₂,
    rw hS₂ at hS₁,
    assumption }
end

end DFA
