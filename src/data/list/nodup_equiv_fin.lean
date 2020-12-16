import data.list.sort
import data.fin

namespace list

variables {α : Type*} [decidable_eq α]

namespace sorted

end sorted

namespace nodup

/-- If `l` has no duplicates, then `list.nth_le` defines a bijection between `fin (length l)` and
the set of elements of `l`. -/
def nth_le_equiv (l : list α) (H : nodup l) : fin (length l) ≃ {x // x ∈ l} :=
{ to_fun := λ i, ⟨nth_le l i i.2, nth_le_mem l i i.2⟩,
  inv_fun := λ x, ⟨index_of ↑x l, index_of_lt_length.2 x.2⟩,
  left_inv := λ i, by simp [H],
  right_inv := λ x, by simp }

variables {l : list α} (H : nodup l) (x : {x // x ∈ l}) (i : fin (length l))

@[simp] lemma coe_nth_le_equiv_apply : (H.nth_le_equiv l i : α) = nth_le l i i.2 := rfl
@[simp] lemma coe_nth_le_equiv_symm_apply : ((H.nth_le_equiv l).symm x : ℕ) = index_of ↑x l := rfl

end nodup

namespace sorted

variables [preorder α] {l : list α}

lemma nth_le_mono (h : l.sorted (≤)) :
  monotone (λ i : fin l.length, l.nth_le i i.2) :=
λ i j, nth_le_of_sorted_of_le h

lemma nth_le_strict_mono (h : l.sorted (<)) :
  strict_mono (λ i : fin l.length, l.nth_le i i.2) :=
λ i j, pairwise_iff_nth_le.1 h i j j.2

/-- If `l` is a list sorted w.r.t. `(<)`, then `list.nth_le` defines an order isomorphism between
`fin (length l)` and the set of elements of `l`. -/
def nth_le_iso (l : list α) (H : sorted (<) l) : fin (length l) ≃o {x // x ∈ l} :=
{ to_equiv := H.nodup.nth_le_equiv l,
  map_rel_iff' := λ i j, H.nth_le_strict_mono.le_iff_le.symm }

variables (H : sorted (<) l) {x : {x // x ∈ l}} {i : fin l.length}

@[simp] lemma coe_nth_le_iso_apply : (H.nth_le_iso l i : α) = nth_le l i i.2 := rfl
@[simp] lemma coe_nth_le_iso_symm_apply : ((H.nth_le_iso l).symm x : ℕ) = index_of ↑x l := rfl

end sorted
end list
