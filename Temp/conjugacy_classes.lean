import Mathlib

#check Algebra.compHom

abbrev List.range_zmod {k : ℕ} (n : ℕ) : List (ZMod k) := List.range n

@[simp]
theorem mem_range_zmod_iff {n : ℕ} [NeZero n] [NeZero k] {i : ZMod k} (n_lt : n > k) : i ∈ List.range_zmod n <-> i.val < n := by
  simp
  constructor
  · intro h
    let ⟨a, ha⟩ := h
    simp [ha.2]
    apply lt_trans ?_ n_lt
    apply Nat.mod_lt
    exact Nat.pos_of_neZero k
  · intro h
    use i.val
    aesop

lemma List.get_find? {α : Type} [DecidableEq α] (l : List α) (p : α → Prop) [DecidablePred p] (h : (List.find? p l).isSome = true) : p $ (List.find? p l).get h  := by
  rw [Option.isSome_iff_exists] at h
  let ⟨a, ha⟩ := h
  have := (List.find?_some ha)
  simp_rw [ha]
  simp_all only [Option.some.injEq, exists_eq', decide_eq_true_eq, Option.get_some]

lemma List.get_findSome?_eq_if_unique {α : Type} [DecidableEq α] (l : List α) (f : α → Option β) (h : (List.findSome? f l).isSome = true) (a : β) : (∀ x ∈ l, (f x).isSome = true -> f x = a) -> (List.findSome? f l).get h = a  := by
  intro h1
  rw [<-Option.some_inj]
  simp
  rw [Option.isSome_iff_exists] at h
  let ⟨x, hx⟩ := h
  have := List.exists_of_findSome?_eq_some hx
  let ⟨b, hb⟩ := this
  specialize h1 b hb.1 (by aesop)
  aesop
@[simp]
theorem DihedralGroup.sr_inv {n : ℕ} (i : ZMod n) : (DihedralGroup.sr i)⁻¹ = DihedralGroup.sr i := by
  apply_fun (fun x => (sr i) * x)
  aesop
  exact mul_right_injective (sr i)

lemma DihedralGroup.conj_classes_r_eq {k : ℕ} (i j : ZMod (2 * k + 1))
  (h_le : i.val ≤ k) (h_le' : j.val ≤ k)
 : (ConjClasses.mk $ DihedralGroup.r i) = (ConjClasses.mk $ DihedralGroup.r j) -> i = j := by
  intro h
  rw [ConjClasses.mk_eq_mk_iff_isConj] at h
  simp at h
  let ⟨c, hc⟩ := h
  match c with
  | DihedralGroup.r s =>
    simp at hc
    apply_fun (fun x => x * (DihedralGroup.r s)) at hc
    group at hc
    simp at hc
    simp_rw [add_comm] at hc
    aesop
  | DihedralGroup.sr s =>
    simp at hc
    apply_fun (fun x => x.val) at hc
    by_cases ne_zero: NeZero i
    · rw [ZMod.val_neg_of_ne_zero] at hc
      omega
    · have : i = 0 := not_neZero.mp ne_zero
      subst i
      simp at hc
      symm
      rw [<-ZMod.val_eq_zero]
      exact hc.symm

-- ConjClasses is either {r^{\plusminus i} of {s r^{k} | k}
noncomputable def conjugacy_classes_of_D_2k_plus_1 (k : ℕ) [NeZero k] : ConjClasses (DihedralGroup (2 * k + 1)) ≃ Option (Fin (k + 1)) := Equiv.mk (
  fun (cl : ConjClasses (DihedralGroup (2 * k + 1))) => if h : (ConjClasses.mk $ DihedralGroup.sr 0) = cl then none
  -- if $cl$ != $[sr]$, we will show $\exists i, cl = [r^i]$
  -- choose an element in $cl$, if $ele = r^i, then cl = [r^i]$
    else
      (
        let exists_i : cl ∈ List.map (fun i => ConjClasses.mk $ DihedralGroup.r i) (List.range_zmod (k + 1)) := by
          simp
          let ⟨ele, hele⟩ := ConjClasses.exists_rep cl
          match ele with
          | DihedralGroup.r i =>
            -- if i <= k, then choose i, else we choose -i.val and use s r^(-i) s^(-1) = r^(i)
            use if i.val <= k then i.val else -i.val
            constructor
            · use if i.val <= k then i.val else (-i).val
              -- gen by aesop
              subst hele
              simp_all only [ZMod.natCast_val, ZMod.cast_id', id_eq, Nat.cast_ite, and_true]
              split
              next h_1 => omega
              next h_1 =>
                simp_all only [not_le]
                have : NeZero i := by
                  rw [neZero_iff]
                  aesop
                rw [ZMod.val_neg_of_ne_zero]
                simp
                omega
            · rw [<-hele]
              rw [ConjClasses.mk_eq_mk_iff_isConj]
              simp
              use if i.val <= k then 1 else DihedralGroup.sr 1
              group
              simp
              aesop
          | DihedralGroup.sr i =>
            -- we show that every s r^i are in the same class
            absurd h
            rw [<-hele]
            rw [ConjClasses.mk_eq_mk_iff_isConj]
            simp
            -- we use ?_ to calculation, which shows that we only need w + w = i
            -- use DihedralGroup.sr ?_
            -- simp
            use DihedralGroup.sr ((ZMod.inv (2 * k + 1) 2) * i)
            simp
            rw [<-add_mul, <-two_mul]
            show (2 * 2⁻¹) * i = _
            rw [ZMod.mul_inv_eq_gcd]
            rw [show (2: ZMod (2 * k + 1)) = (2: ℕ) from rfl]
            rw [ZMod.val_natCast_of_lt]
            simp
            have : k ≠ 0 := by exact Ne.symm (NeZero.ne' k)
            omega
        some ⟨((List.find? (fun i => (ConjClasses.mk $ DihedralGroup.r i) = cl) (List.range_zmod (k := 2 * k + 1) (k + 1))).get (by
          simp at *
          have := exists_i
          simp at this
          aesop
        )).val , by
          generalize_proofs p1 p2
          have := List.get_find?_mem _ _ p2
          simp at this
          simp
          let ⟨a, ha⟩ := this
          rw [ha.2]
          simp [ha.1]
          rw [Nat.mod_eq_of_lt]
          all_goals omega
        ⟩
      )
) (
  fun i => match i with
  | none => ConjClasses.mk $ DihedralGroup.sr 0
  | some i => ConjClasses.mk $ DihedralGroup.r i
) (by
  intro x
  by_cases h: (ConjClasses.mk $ DihedralGroup.sr 0) = x <;> simp only [h]
  simp
  simp only [↓reduceDIte]
  generalize_proofs p1 p2
  have := List.get_find? _ _ p2
  aesop
) (by
  -- the main goal is the classes we construct are actually different
  intro x
  simp
  match x with
  | none => simp
  | some i =>
    simp
    use (
      by
        intro h
        rw [ConjClasses.mk_eq_mk_iff_isConj] at h
        simp at h
        let ⟨c, hc⟩ := h
        match c with
        | DihedralGroup.r j =>
          simp at hc
          apply_fun (fun x => x * (DihedralGroup.r j)) at hc
          group at hc
          simp at hc
        | DihedralGroup.sr j =>
          simp at hc
      )
    apply Fin.eq_of_val_eq
    simp
    let i1: ZMod (2 * k + 1) := i
    have i1_eq : i.val = i1.val := by
      unfold i1
      simp
      rw [Nat.mod_eq_of_lt]
      omega
    simp_rw [i1_eq]
    simp
    apply congr_arg
    apply List.get_findSome?_eq_if_unique
    intro x hx
    simp
    intro h
    have := DihedralGroup.conj_classes_r_eq x i1 ?_ ?_ h
    exact ⟨h, this⟩
    simp at hx
    simp
    rw [Nat.mod_eq_of_lt]
    omega
    omega
    rw [<-i1_eq]
    omega

)
