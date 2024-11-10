import Mathlib
-- Obviously, for any Matrix $A \in G$, we have $A = (A_{1 1} I) (A / A_{1 1}) \in D \times U$
-- it is trivial on math, but many related concepts are lacking in lean at the moment
variable (m: ℕ) (F: Type*) [Field F] [NeZero m]
abbrev InvertibleUpperTriangular := {A: Matrix (Fin m) (Fin m) F // A.BlockTriangular id ∧ ∀i: Fin m, A i i ≠ 0}

@[simp]
theorem invertibleUpperTriangular_def (A: InvertibleUpperTriangular m F) : A.val.BlockTriangular id ∧ ∀i: Fin m, A.val i i ≠ 0 := A.property

theorem invertibleUpperTriangular_element {A: InvertibleUpperTriangular m F} {i j : Fin m} (h: i > j) : A.val i j = 0 := by
  have := A.property.1
  unfold Matrix.BlockTriangular at this
  exact this h
#leansearch "a * b = c means b = a⁻¹ * c on a field?"

noncomputable instance invertibleUpperTriangular_invertible (A: InvertibleUpperTriangular m F) : Invertible A.val := by
  apply Matrix.invertibleOfIsUnitDet
  rw [Matrix.det_of_upperTriangular]
  simp
  simp [Finset.prod_ne_zero_iff]
  exact A.property.1

-- inverse of upper triangular matrix is upper triangular
theorem inverse_of_invertibleUpperTriangular_is_invertibleUpperTriangular_row_i
  (A: InvertibleUpperTriangular m F) (i: Fin m) : ∀ j ≤ i, (A.val⁻¹) i j = if i = j then (A.val i i)⁻¹ else 0 := by
  intro j hj
  -- expands multiplication of matrix inverse
  have : (A.val * A.val⁻¹) = 1 := Matrix.mul_inv_of_invertible _
  -- have ij_neq : i ≠ j := Ne.symm (Fin.ne_of_lt hj)
  apply congr_fun (a := i) at this
  -- have this2 := this
  apply congr_fun (a := j) at this
  -- apply congr_fun (a := i) at this2
  rw [Matrix.mul_apply] at this

  let last_row: Fin m := ⟨m - 1, by norm_num; exact Nat.pos_of_neZero m⟩
  have lt_last_row (j: Fin m) : last_row ≠ j → j < last_row := by
    intro h
    simp [Fin.lt_def]
    simp [Fin.ne_iff_vne] at h
    have := Fin.isLt j
    omega
  -- for the last row, the result is directly from the expands of matrix multiplication
  by_cases h: i = last_row
  · rw [Finset.sum_eq_single_of_mem (a := i)] at this
    simp [Matrix.one_apply] at this
    apply_fun (fun x => (A.val i i)⁻¹ * x) at this
    simp at this
    exact this
    -- other goals are trivial
    simp
    intro b _ hb
    have : b < i := h.symm ▸ (lt_last_row b (by rw [<-h]; exact fun a ↦ hb (id (Eq.symm a))))
    simp [invertibleUpperTriangular_element m F this]
  · -- for other rows, the result comes from the results of below rows
    have i_lt: i < last_row := lt_last_row i (fun a ↦ h (id (Eq.symm a)))
    simp [Matrix.one_apply] at this
    -- actually, only one element of the sum is non zero
    rw [Finset.sum_eq_single_of_mem (a := i)] at this
    apply_fun (fun x => (A.val i i)⁻¹ * x) at this
    simp at this
    exact this
    simp
    intro b _ hb
    have := lt_or_gt_of_ne hb
    rcases this with (hb | hb)
    · -- for b < i, A i b = 0 from the definition of invertible upper triangular matrix
      simp [invertibleUpperTriangular_element m F hb]
    · -- for b > i, we have b > j then recusively A⁻¹ b j = 0
      have := inverse_of_invertibleUpperTriangular_is_invertibleUpperTriangular_row_i A b j (by omega)
      have bj_neq: b ≠ j := by omega
      simp [this, bj_neq]
-- manually claim the termination term
termination_by m - i


-- the diagonal elements of the product of two invertible upper triangular matrices are the product of the diagonal elements of the two matrices
theorem invertibleUpperTriangular_mul_diag {A B: InvertibleUpperTriangular m F} {i: Fin m} : (A.val * B.val) i i = A.val i i * B.val i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single_of_mem
  exact Finset.mem_univ i
  intro b _ hb
  apply lt_or_gt_of_ne at hb
  rcases hb with hb | hb <;> rw [invertibleUpperTriangular_element m F hb] <;> simp


noncomputable instance : Group (InvertibleUpperTriangular m F) where
  mul A B := ⟨A.val * B.val, by
    constructor
    apply Matrix.BlockTriangular.mul <;> simp only [invertibleUpperTriangular_def]
    intro i
    rw [invertibleUpperTriangular_mul_diag]
    simp
    ⟩
  mul_assoc A B C := by
    apply Subtype.eq
    exact mul_assoc _ _ _
  one := ⟨1, by
    constructor
    exact Matrix.blockTriangular_one
    simp
  ⟩
  one_mul A := by
    apply Subtype.eq
    exact one_mul _
  mul_one A := by
    apply Subtype.eq
    exact mul_one _
  inv A := ⟨A.val⁻¹, by
    have := inverse_of_invertibleUpperTriangular_is_invertibleUpperTriangular_row_i m F A
    unfold Matrix.BlockTriangular
    simp
    -- just some easy transformation
    constructor
    · intro i j h
      specialize this i j (by omega)
      have ij_neq: i ≠ j := by omega
      simp [ij_neq] at this
      exact this
    · intro i
      specialize this i i (by omega)
      simp [this]
  ⟩
  inv_mul_cancel A := by
    apply Subtype.eq
    show A.val⁻¹ * A.val = 1
    exact Matrix.inv_mul_of_invertible A.val

@[simp]
theorem invertibleUpperTriangular_one_coe : (1: InvertibleUpperTriangular m F).val = 1 := rfl

@[simp]
theorem invertibleUpperTriangular_mul_coe (A B: InvertibleUpperTriangular m F) : (A * B).val = A.val * B.val := rfl

@[simp]
theorem invertibleUpperTriangular_inv_coe (A: InvertibleUpperTriangular m F) : (A⁻¹).val = A.val⁻¹ := rfl

@[reducible]
def num_matrix (k: F) [NeZero k] : InvertibleUpperTriangular m F := ⟨k • (1: Matrix (Fin m) (Fin m) F), by
    unfold Matrix.BlockTriangular
    simp [Matrix.one_apply]
    aesop
  ⟩

theorem num_matrix_mul {k: F} [NeZero k] {A: InvertibleUpperTriangular m F}: ((num_matrix m F k) * A).val = k • A.val := by
  simp

-- contruct a subgroup of number matrices
def subgroup_D : Subgroup (InvertibleUpperTriangular m F) where
  carrier := {A: InvertibleUpperTriangular m F| ∃ k: F, ∃ne: NeZero k, A = num_matrix m F k}
  one_mem' := by
    use 1
    use NeZero.one
    simp [num_matrix]
    rfl
  mul_mem' := by
    -- (k1 • 1) * (k2 • 1) = (k1 * k2) • 1
    intro a b ha hb
    simp [] at *
    let ⟨k1, ⟨nzk1, hk1⟩⟩ := ha
    let ⟨k2, ⟨nzk2, hk2⟩⟩ := hb
    use k1 * k2
    use NeZero.mul
    rw [hk1, hk2]
    -- transfer the multiplication of scalar to matrix
    apply Subtype.eq
    show (k1 • 1) * (k2 • 1) = (k1 * k2) • 1
    simp [<-mul_smul]
    rw [mul_comm]
  inv_mem' := by
    -- (k • 1)⁻¹ = k⁻¹ • 1
    intro a ha
    simp [num_matrix] at *
    let ⟨k, ⟨nzk, hk⟩⟩ := ha
    use k⁻¹
    use ?_
    rw [hk]
    apply Subtype.eq
    show (k • 1)⁻¹ = k⁻¹ • 1
    apply Matrix.inv_eq_left_inv
    simp [<-mul_smul]
    rw [Field.mul_inv_cancel k nzk.out]
    simp
    apply NeZero.mk
    exact inv_ne_zero nzk.out

-- construct the subgroup every matrix in which has all equal diagonal elements
def subgroup_G : Subgroup (InvertibleUpperTriangular m F) where
  carrier := {A: InvertibleUpperTriangular m F| ∀ i j: Fin m, A.val i i = A.val j j}
  one_mem' := by
    simp [Matrix.one_apply]
  mul_mem' := by
    -- easy from invertibleUpperTriangular_mul_diag
    intro a b ha hb
    simp at *
    intro i j
    simp [invertibleUpperTriangular_mul_diag]
    rw [ha i, hb j]
  inv_mem' := by
    -- easy from inverse_of_invertibleUpperTriangular_is_invertibleUpperTriangular_row_i
    intro a ha
    simp at *
    intro i j
    simp [inverse_of_invertibleUpperTriangular_is_invertibleUpperTriangular_row_i m F a ]
    rw [ha j]

-- construct the subgroup every matrix in which has all one diagonal elements
def subgroup_U : Subgroup (InvertibleUpperTriangular m F) where
  carrier := {A: InvertibleUpperTriangular m F| ∀ i: Fin m, A.val i i = 1}
  one_mem' := by
    simp [Matrix.one_apply]
  mul_mem' := by
    intro a b ha hb
    simp at *
    intro i
    -- easy from invertibleUpperTriangular_mul_diag
    simp [invertibleUpperTriangular_mul_diag]
    simp [ha i, hb i]
  inv_mem' := by
    -- easy from inverse_of_invertibleUpperTriangular_is_invertibleUpperTriangular_row_i
    intro a ha
    simp at *
    intro i
    simp [inverse_of_invertibleUpperTriangular_is_invertibleUpperTriangular_row_i m F a]
    simp [ha i]

-- final theroem, the inner product of D and U is equal to G
#leansearch "if H ≤ L and K ≤ L, then H ⊔ K <= L ?"
#leansearch "inv_eq_of_mul_eq_one?"
theorem subgroup_D_mul_U_eq_G : subgroup_D m F ⊔ subgroup_U m F = subgroup_G m F := by
  -- just use A = (A_{1 1} I) (A / A_{1 1}) \in D \times U
  apply le_antisymm
  · -- if H ≤ L and K ≤ L, then H ⊔ K <= L
    apply sup_le
    · -- D ≤ G
      intro A hA
      simp [subgroup_G, subgroup_D] at *
      let ⟨k, ⟨_, hk⟩⟩ := hA
      simp [num_matrix] at hk
      rw [hk]
      simp
    · -- U ≤ G
      intro A hA
      simp [subgroup_G, subgroup_U] at *
      simp [hA]
  · rw [SetLike.le_def] -- to member relation
    intro A hA
    -- show $A = (A_{1 1} I) (A / A_{1 1}) \in D \times U$ is enough for A ∈ subgroup_D ⊔ subgroup_U
    letI : NeZero (A.val 0 0) := by
      have := A.2.2 0
      exact { out := this }
    letI : NeZero (A.val 0 0)⁻¹ := by
      apply NeZero.mk
      exact inv_ne_zero this.out
    have : A = (num_matrix m F (A.val 0 0)) * ((num_matrix m F (A.val 0 0))⁻¹ * A) := by
      simp
    rw [this]
    apply Subgroup.mul_mem_sup
    · simp [subgroup_D]
      use A.val 0 0
    · simp [subgroup_G] at hA
      have : (num_matrix m F (A.val 0 0))⁻¹ = num_matrix m F (A.val 0 0)⁻¹ := by
        apply Eq.symm
        apply eq_inv_of_mul_eq_one_left
        apply Subtype.eq
        simp
      simp [subgroup_U, this]
      intro i
      simp [hA 0 i]
