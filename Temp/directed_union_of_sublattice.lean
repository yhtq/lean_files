import Mathlib
#leansearch "directed union of sublattice?"
-- If $a, b \in \bigcup A_i$, we can suppose $a \in A_{i}$ and $b \in A_{j}$, then $a \in A_{k}$ and $b \in A_{k}$ for some $k$, then $a, b \in A_{k} \Rightarrow a \sqcup b \in A_k, a \sqcap b \in A_k$, which means $a \sqcup b \in \bigcup A_{i}$ and $a \sqcap b \in \bigcup A_{i}$
variable
    {A I: Type*} [Lattice A]
    (i_map: I -> Sublattice A)

abbrev isDirected: Prop := ∀ (i j: I), ∃ k, (i_map i: Set A) ∪ i_map j ≤ i_map k

def directed_union_of_sublattice (h: isDirected i_map): Sublattice A where
  carrier := ⋃ i, i_map i
  supClosed' := by
    intro a ha b hb
    -- $a \in \bigcup A_i$ iff $a \in A_i$ for some $i$
    simp at *
    let ⟨i, hi⟩ := ha
    let ⟨j, hj⟩ := hb
    let ⟨k, hk⟩ := h i j
    -- use the index k which is bigger than i and j
    use k
    have : a ∈ (i_map i: Set A) ∪ i_map j := Set.mem_union_left (↑(i_map j)) hi
    have a_in : a ∈ i_map k := hk this  -- obviously $a \in A_k$
    have : b ∈ (i_map i: Set A) ∪ i_map j := Set.mem_union_right (↑(i_map i)) hj
    have b_in : b ∈ i_map k := hk this  -- obviously $b \in A_k$
    exact (i_map k).supClosed a_in b_in -- sublattice is supClosed, so $a \sqcup b \in A_k$
  infClosed' := by
    -- nearly the same as supClosed
    intro a ha b hb
    simp at *
    let ⟨i, hi⟩ := ha
    let ⟨j, hj⟩ := hb
    let ⟨k, hk⟩ := h i j
    use k
    have : a ∈ (i_map i: Set A) ∪ i_map j := Set.mem_union_left (↑(i_map j)) hi
    have a_in : a ∈ i_map k := hk this
    have : b ∈ (i_map i: Set A) ∪ i_map j := Set.mem_union_right (↑(i_map i)) hj
    have b_in : b ∈ i_map k := hk this
    exact (i_map k).infClosed a_in b_in

example (is_directed: isDirected i_map): (directed_union_of_sublattice i_map is_directed).carrier = ⋃ i, i_map i := rfl
