import Mathlib

open Classical

-- 1. Take the resultant of two polynomial:
--     $$
--     R(x_1) = u(x_1, x_2)f(x_1, x_2) + v(x_1, x_2) g(x_1, x_2)
--     $$
-- 2. if $f, g$ have infinitely many common roots, then $R(x_1) = 0$, $(k[x_1])[x_2]$ is a integral domain gives that $f, g$ have a common divisor, which is absurd.
-- remark: resultant is not implemented in mathlib yet, so we wiil use coprime on $(k(x_1))[x_2]$ (which holds if f and g are primitives, but actually we can just take primPart of them) to get a polynomial close to resultant
-- at the same time, the field extension can cause some trouble because coprime elements could not be coprime in ring extension, but when we consider coprime on $(k(x_1))[x_2]$, field extension keeps coprime.

-- a ringHom version of MvPolynomial.eval_eq_eval_mv_eval'
lemma eval_eq_eval_mv_eval_ringHom
    {R : Type u} [CommSemiring R] {n : ℕ} (s : Fin n → R) (y : R):
    (MvPolynomial.eval (Fin.cons y s))  =
    (Polynomial.evalRingHom y).comp
      ((Polynomial.mapRingHom (MvPolynomial.eval s)).comp ((MvPolynomial.finSuccEquiv R n))
      ) := by
  apply RingHom.ext
  intro f
  apply MvPolynomial.eval_eq_eval_mv_eval'

lemma Polynomial.eval₂RingHom_map.{u, v, w} {R : Type u} {S : Type v} {T : Type w} [CommRing R] {p : Polynomial R} [CommRing S]
  (f : R →+* S) [CommRing T] (g : S →+* T) (x : T) :
  Polynomial.eval₂RingHom g x (Polynomial.map f p) = Polynomial.eval₂RingHom (g.comp f) x p := by
    simp [coe_eval₂RingHom]
    exact eval₂_map f g x

universe u_1

lemma motive_one (motive: Fin 1 -> Sort u_1) : motive = fun i => if i = 0 then motive 0 else motive 1 := by
  funext i
  fin_cases i <;> simp

variable {K : Type*} [Field K]

noncomputable def common_denom  (a: Polynomial (RatFunc K)) :=
  ∏ n ∈ a.support, (a.coeff n).denom

lemma coeff_dvd_common_denom (a: Polynomial (RatFunc K)) (i: ℕ) (hi: i ∈ a.support):
  (a.coeff i).denom ∣ common_denom a := Finset.dvd_prod_of_mem  _ hi

theorem common_denom_not_eq_zero {a: Polynomial (RatFunc K)}:
  common_denom a = 0 -> False := by
    intro h
    simp [common_denom] at h
    rw [Finset.prod_eq_zero_iff] at h
    let ⟨i, ⟨hi1, hi2⟩⟩ := h
    have := RatFunc.denom_ne_zero (a.coeff i)
    contradiction

theorem common_denom_ne_zero {a: Polynomial (RatFunc K)}:
  common_denom a ≠ 0 := by
    intro h
    exact common_denom_not_eq_zero h

lemma eval_common_denom_dvd (a: Polynomial (RatFunc K)) (k: K):
  (Polynomial.eval (RatFunc.C k) a).denom ∣ common_denom a := by
    show (Polynomial.eval (algebraMap (Polynomial K) (RatFunc K)  (Polynomial.C k)) a).denom ∣ common_denom a
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    -- induction on the monomial in a
    let ps_aux (s: Finset ℕ) := (∑ n ∈ s, a.coeff n * (algebraMap (Polynomial K) (RatFunc K)) (Polynomial.C k) ^ n).denom ∣ ∏ n ∈ s, (a.coeff n).denom
    have : ps_aux a.support := by
      apply Finset.induction_on
      · simp [ps_aux]
      · simp [ps_aux]
        intro i s1 hs1 hind
        -- do some number theory calculation
        simp only [Finset.sum_insert hs1, Finset.prod_insert hs1]
        apply dvd_trans (RatFunc.denom_add_dvd _ _)
        apply mul_dvd_mul ?_ hind
        apply dvd_trans (RatFunc.denom_mul_dvd _ _)
        rw [show (RatFunc.C k) ^ i = RatFunc.C (k ^ i) from
          Eq.symm (RingHom.map_pow _ _ _)]
        rw [RatFunc.denom_C]
        simp
    exact this


-- a simple lemma to remove the common denominator of a polynomial, but we must do some manually transformation
lemma eq_common_denom_mul_algebraMap (a: Polynomial (RatFunc K)) :
  ∃ a': Polynomial (Polynomial K), (Polynomial.C ((algebraMap (Polynomial K) (RatFunc K)) (common_denom a))) * a = (Polynomial.map (algebraMap (Polynomial K) (RatFunc K)) a')  := by
    let cd' := Polynomial.map (algebraMap K (RatFunc K)) (common_denom a)
    let f_aux (i: ℕ) : i ∈ a.support -> Polynomial K := fun hi => ((a.coeff i) * ((algebraMap (Polynomial K) (RatFunc K)) (common_denom a))).num
    have f_aux_non_zero : ∀ i hi, ¬f_aux i hi = 0 := by
      intro i hi
      unfold f_aux
      simp at hi
      simp [hi]
      unfold common_denom
      rw [Finset.prod_eq_zero_iff]
      simp [RatFunc.denom_ne_zero]
    have f_aux_eq (i: ℕ) : (h: i ∈ a.support) -> (a.coeff i) * ((algebraMap (Polynomial K) (RatFunc K)) (common_denom a)) = algebraMap (Polynomial K) (RatFunc K) (f_aux i h) := by
      intro hi
      letI : DecidableEq K := Classical.decEq K
      letI : DecidableEq (RatFunc K) := Classical.decEq _
      unfold f_aux
      generalize h: (a.coeff i) * ((algebraMap (Polynomial K) (RatFunc K)) (common_denom a)) = coeff'
      nth_rw 1 [<-RatFunc.num_div_denom coeff']
      -- we use the trick that if denom = 1, then it equal to its num
      have : coeff'.denom = 1 := by
        rw [<-h]
        rw [<-RatFunc.num_div_denom (a.coeff i)]
        rw [div_mul_eq_mul_div]
        rw [<-RingHom.map_mul]
        rw [RatFunc.denom_div]
        have : gcd ((a.coeff i).num * common_denom a) (a.coeff i).denom = (a.coeff i).denom := by
          rw [gcd_eq_right_iff]
          apply dvd_trans (coeff_dvd_common_denom a i hi)
          exact dvd_mul_left _ _
          exact Polynomial.Monic.normalize_eq_self (RatFunc.monic_denom (a.coeff i))
        rw [this]
        simp [RatFunc.denom_ne_zero]
        exact RatFunc.denom_ne_zero _
      simp [this]
    use Polynomial.ofFinsupp
      {
        support := a.support,
        toFun := fun i => if hi : (i ∈ a.support) then (f_aux i hi) else 0,
        mem_support_toFun := by
          intro i
          simp
          intro _
          exact common_denom_ne_zero
      }
    -- show every coefficient is equal
    apply Polynomial.ext
    intro n
    rw [Polynomial.coeff_C_mul]
    simp
    by_cases h: n ∈ a.support <;> simp at h <;> simp [h]
    rw [<-f_aux_eq]
    rw [mul_comm]
    simp [h]


-- a weak version of the following theorem
theorem coprime_polynomial_polynomial_have_finitely_many_common_roots_0
    (f g: Polynomial (Polynomial K))
    (coprime: IsCoprime (Polynomial.map (algebraMap (Polynomial K) (RatFunc K)) f) (Polynomial.map (algebraMap (Polynomial K) (RatFunc K)) g))
    :
    {x: K | ∃ y: K, Polynomial.evalEval x y f = 0 ∧ Polynomial.evalEval x y g = 0}.Finite := by
      letI : DecidableEq K := Classical.decEq K
      letI : DecidableEq (RatFunc K) := Classical.decEq _
      by_contra if_infinite_common_roots
      -- if the set is finite
      simp [<-Set.not_infinite] at if_infinite_common_roots
      let ⟨a, ⟨b, hab⟩⟩ := coprime
      -- we will show that common_denoms eval to zero on infinitely many points, then is equal to zero, which is absurd
      let common_denoms := (common_denom a) * (common_denom b)
      have eval_common_denoms_zero
        (x: K)
        (h: ∃ y: K, Polynomial.evalEval x y f = 0 ∧ Polynomial.evalEval x y g = 0)
        : Polynomial.eval x common_denoms = 0 := by
          -- denoms must eval to zero
          let ⟨y, ⟨hf, hg⟩⟩ := h
          apply_fun (Polynomial.eval (RatFunc.C y)) at hab
          simp  at hab
          apply_fun (RatFunc.eval (RingHom.id _) x) at hab
          simp  at hab
          by_contra eq_zero
          have mul_algebraMap_donom (f: RatFunc K) (h: Polynomial K) :
            (f * algebraMap (Polynomial K) (RatFunc K) h).denom ∣ f.denom := by
              nth_rw 1 [<-RatFunc.num_div_denom f]
              rw [div_mul_eq_mul_div]
              rw [<-RingHom.map_mul]
              exact RatFunc.denom_div_dvd (f.num * h) f.denom
          rw [RatFunc.eval_add, RatFunc.eval_mul, RatFunc.eval_mul] at hab
          have (f: Polynomial (Polynomial K)) :
            RatFunc.eval (RingHom.id K) x ((Polynomial.aeval (RatFunc.C y)) f) = f.evalEval x y :=
            by
              rw [show RatFunc.C y = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C y) from rfl]
              rw [Polynomial.aeval_algebraMap_apply]
              simp
              rfl
          -- have mul_aveal_denom (f: RatFunc K) (h: Polynomial (Polynomial))
          simp [this f, this g, hf, hg] at hab  -- close the goal if denoms eval to nonzero
          all_goals simp [show Polynomial.eval₂ (RingHom.id _) = Polynomial.eval from rfl]
          all_goals rw [show RatFunc.C y = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C y) from rfl]
          all_goals try rw [Polynomial.aeval_algebraMap_apply]
          all_goals simp  -- close the goal of denoms of f and g
          all_goals apply not_imp_not.mpr (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero ?_) eq_zero
          all_goals unfold common_denoms
          all_goals try apply dvd_trans (eval_common_denom_dvd _ _) <;> simp  -- close the goal without f *
          all_goals apply  dvd_trans (mul_algebraMap_donom _ _) <;> apply dvd_trans (eval_common_denom_dvd _ _) <;> simp -- close the goal with f *
      let roots_x := {x: K | ∃ y: K, Polynomial.evalEval x y f = 0 ∧ Polynomial.evalEval x y g = 0}
      have : {x | common_denoms.IsRoot x}.Infinite := by
        have : roots_x ⊆ {x | common_denoms.IsRoot x} := by
          intro x hx
          simp [roots_x] at hx ⊢
          exact eval_common_denoms_zero _ hx
        exact Set.Infinite.mono eval_common_denoms_zero if_infinite_common_roots
      apply Polynomial.eq_zero_of_infinite_isRoot at this -- then common_denoms = 0
      simp [common_denoms] at this  -- means common_denom a = 0 or common_denom b = 0
      exact Or.elim this common_denom_ne_zero common_denom_ne_zero

-- if two primtive polynomials are coprime, then they are also coprime in the fraction field. The key theorem is already in mathlib but there are still some transformation to  do
theorem coprime_ratFunc_of_relPrime
    (f g: Polynomial (Polynomial K))
    (coprime: IsRelPrime f g)
    (prim_f: f.IsPrimitive)
    (prim_g: g.IsPrimitive)
 : IsCoprime (Polynomial.map (algebraMap (Polynomial K) (RatFunc K)) f) (Polynomial.map (algebraMap (Polynomial K) (RatFunc K)) g) := by
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  rw [<-isRelPrime_iff_isCoprime]
  intro d hd1 hd2
  let ⟨d', hd'⟩ := eq_common_denom_mul_algebraMap d -- remove the common denominator of d
  -- d' can not be zero
  have d'_ne_zero : ¬ d' = 0 := by
    intro h
    simp [h] at hd'
    simp [common_denom_ne_zero] at hd'
    simp [hd'] at hd1 hd2
    rw [Polynomial.map_eq_zero_iff] at hd1 hd2
    · rw [hd1, hd2] at coprime
      apply IsRelPrime.ne_zero_or_ne_zero at coprime
      simp [hd1, hd2] at coprime
    all_goals exact RatFunc.algebraMap_injective K
  let common_denom' := Polynomial.C ((algebraMap (Polynomial K) (RatFunc K)) (common_denom d))
  apply mul_dvd_mul_left common_denom' at hd1
  apply mul_dvd_mul_left common_denom' at hd2
  rw [hd'] at hd1 hd2
  have : IsUnit common_denom' := by
    apply Polynomial.isUnit_C.mpr
    simp
    exact common_denom_ne_zero
  rw [IsUnit.dvd_mul_left this] at hd1 hd2
  let d'_prim := d'.primPart  -- take the prim part of d' to use the theorem
  have : (Polynomial.map (algebraMap (Polynomial K) (RatFunc K)) d'_prim) ∣ Polynomial.map (algebraMap (Polynomial K) (RatFunc K)) d' := by
    apply Polynomial.map_dvd
    exact d'.primPart_dvd
  apply dvd_trans this at hd1
  apply dvd_trans this at hd2
  -- use the key theorem which pass Polynomial.map (algebraMap R K) p ∣ Polynomial.map (algebraMap R K) q tp p | q if p and q are primitives, simiarly to Gauss lemma
  rw [<-Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map _ (Polynomial.isPrimitive_primPart d')] at hd1 hd2 <;> try assumption
  have := coprime hd1 hd2 -- dvd shows d'.primPart is a unit
  rw [Polynomial.eq_C_content_mul_primPart d'] at hd'
  rw [Polynomial.map_mul] at hd'
  apply_fun IsUnit at hd' -- show two sides of hd' are both unit, and then d is unit
  simp  at hd'
  rw [Polynomial.content_eq_zero_iff] at hd'
  simp [d'_ne_zero, common_denom_ne_zero] at hd'
  rw [hd']
  rw [<-Polynomial.coe_mapRingHom]
  exact IsUnit.map _ this

noncomputable abbrev algMap_K_to_L (K: Type*) [Field K] (L: Type*) [Field L] [Algebra K L] : (RatFunc K) →+* (RatFunc L) :=
  (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap K L)) (by
        rw [SetLike.le_def]
        intro x h
        simp [mem_nonZeroDivisors_iff] at h
        simp [mem_nonZeroDivisors_iff]
        intro a ha
        simp [ha] at h
        specialize h (Polynomial.C 1)
        simp at h
    ))

-- a simple extension of the above theorem, because is coprime can be easily extended to a field extension
theorem extension_coprime_of_relPrime (L: Type*) [Field L] [Algebra K L]
    (f g: Polynomial (Polynomial K))
    (coprime: IsRelPrime f g)
    (prim_f: f.IsPrimitive)
    (prim_g: g.IsPrimitive)
  :
    let algMap := (algebraMap (Polynomial L) (RatFunc L)).comp (Polynomial.mapRingHom (algebraMap K L))
    IsCoprime (Polynomial.map algMap f) (Polynomial.map algMap g) := by
  extract_lets algMap
  -- transform the theorem to the form of the above theorem
  have (f: Polynomial (Polynomial K)) : Polynomial.map (algMap_K_to_L K L) (Polynomial.map (algebraMap (Polynomial K) (RatFunc K)) f)
    = Polynomial.map algMap f := by
    unfold algMap
    apply Polynomial.ext
    intro n
    simp
    unfold algMap_K_to_L
    rw [RatFunc.coe_mapRingHom_eq_coe_map]
    have : (algebraMap (Polynomial K) (RatFunc K)) (f.coeff n) = (algebraMap (Polynomial K) (RatFunc K)) (f.coeff n) / (algebraMap (Polynomial K) (RatFunc K) 1) := by simp
    rw [this]
    rw [RatFunc.map_apply_div]
    simp
  simp [<-this]
  repeat rw [<-Polynomial.coe_mapRingHom]
  apply IsCoprime.map
  apply coprime_ratFunc_of_relPrime <;> assumption

lemma isCoprime_prim_in_ratFunc_iff
    (L: Type*) [Field L] [Algebra K L]
    (f g: Polynomial (Polynomial K))
    (f_ne_zero : f ≠ 0)
    (g_ne_zero : g ≠ 0)
    (hom: Polynomial (Polynomial K) →+* Polynomial (RatFunc L))
    (C_to_unit: ∀k: (Polynomial K), k ≠ 0 -> IsUnit (hom (Polynomial.C k)))
  : IsCoprime (hom f.primPart) (hom g.primPart) ↔ IsCoprime (hom f) (hom g) := by
    conv =>
      rhs
      rw [Polynomial.eq_C_content_mul_primPart f, Polynomial.eq_C_content_mul_primPart g]
      repeat rw [RingHom.map_mul]
    rw [isCoprime_mul_unit_left_left, isCoprime_mul_unit_left_right]
    all_goals apply C_to_unit; simp [Polynomial.content_eq_zero_iff]; assumption




-- second version of the theorem, which is more close to the result. We will handle the primtive condition and field extension here
theorem coprime_polynomial_polynomial_have_finitely_many_common_roots_1 (L: Type*) [Field L] [Algebra K L]
    (f g: Polynomial (Polynomial K))
    (coprime: IsRelPrime f g)
    (f_ne_zero: f ≠ 0)  -- notice that IsRelPrime f g only proves f, g are not both zero, but if one of them are zero, the result is of course false
    (g_ne_zero: g ≠ 0)
    :
    let algMap := Polynomial.map (Polynomial.mapRingHom (algebraMap K L))
    {x: L | ∃ y: L, Polynomial.evalEval x y (algMap f) = 0 ∧ Polynomial.evalEval x y (algMap g) = 0}.Finite := by
  extract_lets algMap
  have algMap_inj : Function.Injective algMap := by
    apply Polynomial.map_injective
    apply Polynomial.map_injective
    exact NoZeroSMulDivisors.algebraMap_injective K L
  -- before use the theorems before, we must prove the roots set is same after taking the prim part
  -- actually, the content only gives finitely many roots, so do not affect the result
  have :
    {x: L | ∃ y: L, Polynomial.evalEval x y (algMap f) = 0 ∧ Polynomial.evalEval x y (algMap g) = 0}
    ⊆
      (algMap f).content.rootSet L ∪
      (algMap g).content.rootSet L ∪
      {x: L | ∃ y: L, Polynomial.evalEval x y (algMap f).primPart = 0 ∧ Polynomial.evalEval x y (algMap g).primPart = 0} := by
      nth_rw 1 [Polynomial.eq_C_content_mul_primPart (algMap f), Polynomial.eq_C_content_mul_primPart (algMap g)]
      simp [Polynomial.evalEval_C]
      intro x hx
      simp at hx ⊢
      repeat rw [Polynomial.mem_rootSet_of_ne]
      · aesop -- just some boring logic, use aesop to close the goal
      all_goals simp [Polynomial.content_eq_zero_iff]
      all_goals rw [show 0 = algMap 0 by unfold algMap; simp]
      all_goals intro h
      all_goals apply algMap_inj at h;
      all_goals contradiction
  apply Set.Finite.subset ?_ this
  simp [Polynomial.rootSet_finite]
  -- finally, apply the theorem before
  apply coprime_polynomial_polynomial_have_finitely_many_common_roots_0
  have := extension_coprime_of_relPrime L f.primPart g.primPart ?_
  simp [Polynomial.isPrimitive_primPart] at this
  pick_goal 2 -- which is easy
  · apply IsRelPrime.of_dvd_left (y := f) (dvd := Polynomial.primPart_dvd _)
    apply IsRelPrime.of_dvd_right (y := g) (dvd := Polynomial.primPart_dvd _)
    exact coprime
  unfold algMap
  -- the key point is in the fraction field, the content will finally be a unit, which is not a matter
  simp [<-Polynomial.map_map] at this
  generalize hf1 : Polynomial.map (algebraMap (Polynomial L) (RatFunc L)) = f1 at *
  generalize hf2 : Polynomial.map (Polynomial.mapRingHom (algebraMap K L)) = f2 at *
  let hom1 := Polynomial.mapRingHom (algebraMap (Polynomial L) (RatFunc L))
  let hom2 := Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap K L))
  have hom1_lift_unit : ∀ (k : Polynomial L), k ≠ 0 → IsUnit (hom1 (Polynomial.C k)) := by
    intro k hk
    unfold hom1
    simp [hk]
  have hom2_inj (x) : hom2 x = 0 <-> x = 0 := by
    constructor
    · intro h
      rw [<-show hom2 0 = 0 by simp] at h
      rw [Function.Injective.eq_iff] at h
      exact h
      unfold hom2
      exact algMap_inj
    · intro h; simp [h]
  have f_to_hom_1 (x) : f1 x = hom1 x := by rw [<-hf1]; rfl
  have f_to_hom_2 (x) : f2 x = hom2 x := by rw [<-hf2]; rfl
  simp [f_to_hom_1, f_to_hom_2] at this ⊢
  repeat rw [<-RingHom.comp_apply] at this
  rw [isCoprime_prim_in_ratFunc_iff] at this ⊢
  exact this
  -- many remaining goals, but they are boring
  all_goals try (simp [hom2_inj]; assumption)
  intro k hk
  simp
  unfold hom2
  simp
  apply hom1_lift_unit
  simp [hk]

-- a canonical isomorphism between MvPolynomial (Fin 2) K and Polynomial (Polynomial K)
-- but its definition is actually very hard, which brings much trouble
noncomputable def equiv_mv_to_poly : MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) := by
  let equiv_2_to_1 := MvPolynomial.finSuccEquiv K 1
  simp at equiv_2_to_1
  let equiv_1_to_0 := MvPolynomial.finSuccEquiv K 0
  simp at equiv_1_to_0
  let equiv_0_to_K := MvPolynomial.isEmptyAlgEquiv K (Fin 0)
  let equiv_1_to_poly := Polynomial.mapAlgEquiv equiv_0_to_K
  -- to construct a K-algebra equiv from MvPolynomial (Fin 2) K to Polynomial (Polynomial K))
  let equiv := (equiv_2_to_1.trans $ Polynomial.mapAlgEquiv equiv_1_to_0).trans $ Polynomial.mapAlgEquiv equiv_1_to_poly
  exact equiv

-- a (not) simple lemma to handle the evaluation of MvPolynomial, the true version we will use is much harder than this
lemma equiv_eval (f: MvPolynomial (Fin 2) K): ∀ k: Fin 2 -> K,
  MvPolynomial.eval k f = Polynomial.eval (k 1) (Polynomial.eval (Polynomial.C $ k 0) (equiv_mv_to_poly (K := K) f)) := by
    intro k
    -- destruct k to Fin.cons to use MvPolynomial.eval_eq_eval_mv_eval'
    have : k = Fin.cons (k 0) (Fin.cons (k 1) (IsEmpty.elim Fin.isEmpty')) := by
      rw [<-Fin.cons_self_tail k]
      apply Fin.cons_eq_cons.mpr
      simp
      rw [<-Fin.cons_self_tail (Fin.tail k)]
      apply Fin.cons_eq_cons.mpr
      simp
      apply Subsingleton.allEq
    nth_rw 1 [this]
    simp [MvPolynomial.eval_eq_eval_mv_eval']
    -- do some annoying calculation
    unfold equiv_mv_to_poly
    simp [eval_eq_eval_mv_eval_ringHom, AlgEquiv.coe_trans, Polynomial.eval_map, Polynomial.eval₂_map]
    simp [<-Polynomial.coe_mapRingHom, <-Polynomial.coe_eval₂RingHom]
    have : RingHomClass.toRingHom (MvPolynomial.isEmptyAlgEquiv K (Fin 0)) = MvPolynomial.eval (fun a ↦ Fin.isEmpty'.elim a) := by
      apply RingHom.ext
      intro f
      simp
      rfl
    rw [this]
    -- these terms are useless
    generalize ((Polynomial.mapRingHom (MvPolynomial.eval fun a => Fin.isEmpty'.elim a)).comp (RingHomClass.toRingHom (MvPolynomial.finSuccEquiv K 0))) = l
    generalize (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
  (fun i ↦ Fin.cases Polynomial.X (fun k ↦ Polynomial.C (MvPolynomial.X k)) i) f) = f
    -- use evalEval to change the eval order
    rw [Polynomial.coe_eval₂RingHom, <-Polynomial.eval₂_map]
    rw [Polynomial.eval₂_evalRingHom]
    simp
    rw [<-Polynomial.eval_map]

lemma coprime_equiv {L: Type*} [CommRing L] [Algebra K L]
    {equiv: MvPolynomial (Fin 2) K ≃ₐ[K] L} {f g: MvPolynomial (Fin 2) K}
    (coprime: IsRelPrime f g)
     :
  IsRelPrime (equiv f) (equiv g) := by
    intro d hd1 hd2
    rw [<-map_dvd_iff (f := equiv.symm)] at hd1 hd2
    simp at hd1 hd2
    have := coprime hd1 hd2
    simp at this
    exact this

theorem coprime_mvPolynomial_have_finitely_many_common_roots
    -- actually there is a section "Polynomial.Bivariate" in mathlib, but here I manage to use MvPolynomial and do a muanual transformation
    (L: Type*) [Field L] [Algebra K L]
    (f g: MvPolynomial (Fin 2) K)
    (f_ne_zero: f ≠ 0)  -- notice that IsRelPrime f g only proves f, g are not both zero, but if one of them are zero, the result is of course false
    (g_ne_zero: g ≠ 0)
    (coprime: IsRelPrime f g)  -- notice that IsCoprime in Mathlib is defined as $(a) + (b) = 1$, however the meaning in the exercise is more close to have no common divisor.
    :
    {k: Fin 2 -> L | MvPolynomial.aeval k f = 0 ∧ MvPolynomial.aeval k g = 0}.Finite := by
      letI : DecidableEq K := Classical.decEq K
      letI : DecidableEq (RatFunc K) := Classical.decEq _
      by_contra if_infinite_common_roots
      -- if the set is finite
      simp [<-Set.not_infinite] at if_infinite_common_roots
      let roots_x := {x: L | ∃ k: Fin 2 -> L, MvPolynomial.aeval k f = 0 ∧ MvPolynomial.aeval k g = 0 ∧ k 1 = x}
      let roots_y := {y: L | ∃ k: Fin 2 -> L, MvPolynomial.aeval k f = 0 ∧ MvPolynomial.aeval k g = 0 ∧ k 0 = y}
      -- actually, we can wlog assume roots_x is infinite, otherwise we just exchange x and y in f and g
      wlog roots_x_infinite : roots_x.Infinite generalizing f g
      pick_goal 2 -- we will first prove if roots_x is infinite, later we will prove the wlog
      -- to construct a K-algebra equiv from MvPolynomial (Fin 2) K to Polynomial (Polynomial K))
      let equiv := equiv_mv_to_poly (K := K)

      -- these lemmas will be uses many times
      -- use Type* will cause universe error
      have f_ne_zero_equiv {L: Type _} [CommRing L] [Algebra K L] (equiv: MvPolynomial (Fin 2) K ≃ₐ[K] L) : equiv f ≠ 0 := by
        intro h
        apply f_ne_zero
        apply equiv.injective
        simp [h]
      have g_ne_zero_equiv {L: Type _} [CommRing L] [Algebra K L] (equiv: MvPolynomial (Fin 2) K ≃ₐ[K] L) : equiv g ≠ 0 := by
        intro h
        apply g_ne_zero
        apply equiv.injective
        simp [h]

      let f' := equiv f
      let g' := equiv g
      -- map Polynomial (Polynomial K) to Polynomial (FractionRing (Polynomial K))
      let frac_Kx := RatFunc K
      let poly_to_rat := algebraMap (Polynomial K) frac_Kx
      let inj_to_frac := Polynomial.mapAlg (Polynomial K) (frac_Kx)
      have : Function.Injective inj_to_frac := by apply Polynomial.map_injective; exact NoZeroSMulDivisors.algebraMap_injective (Polynomial K) frac_Kx
      let f'_frac := inj_to_frac f'
      let g'_frac := inj_to_frac g'
      let algMap := Polynomial.map (Polynomial.mapRingHom (algebraMap K L))
      have aeval_trans (f: MvPolynomial (Fin 2) K) (k: Fin 2 -> L):
        MvPolynomial.aeval k f = Polynomial.evalEval (k 1) (k 0) (algMap (equiv f)) := by
          have : MvPolynomial.aeval k f = MvPolynomial.eval k (MvPolynomial.map (algebraMap K L) f) := by
            simp
            rfl
          rw [this]
          rw [equiv_eval]
          simp [Polynomial.evalEval]
          apply congr_arg
          apply congr_arg
          unfold equiv_mv_to_poly
          unfold algMap equiv equiv_mv_to_poly
          simp
          generalize hs1: (fun i => Fin.cases Polynomial.X (fun k => Polynomial.C (MvPolynomial.X k)) i: Fin 2 → Polynomial (MvPolynomial (Fin 1) L)) = s1
          -- move algebraMap outward with diffculties
          -- the Fin.cases brought in by finSuccEquiv must be manually handled
          have s1_pass : s1 =
            (Polynomial.mapRingHom (MvPolynomial.map (algebraMap K L))) ∘ (
              (fun i => Fin.cases Polynomial.X (fun k => Polynomial.C (MvPolynomial.X k)) i): Fin 2 → Polynomial (MvPolynomial (Fin 1) K)
              ) := by
            rw [<-hs1]
            ext i n m
            simp
            apply congr_arg
            match i with
            | 0 => simp [Polynomial.coeff_X]
            | 1 =>
              have : (1: Fin 2) = ( ⟨(0: ℕ).succ, by norm_num⟩: Fin 2) := rfl
              repeat rw [this]
              repeat rw [Fin.cases_succ']
              simp [Polynomial.coeff_C]
              rw [apply_ite (f := (MvPolynomial.map (algebraMap K L)))]
              simp
          rw [s1_pass]
          have commute_C {n: ℕ} : ((Polynomial.C.comp MvPolynomial.C).comp (algebraMap K L): K →+* Polynomial (MvPolynomial (Fin n) L)) =
            (Polynomial.mapRingHom (MvPolynomial.map (algebraMap K L))).comp (Polynomial.C.comp MvPolynomial.C) := by
              ext _ _ _
              simp
          rw [commute_C]
          rw [<-MvPolynomial.eval₂_comp_left]
          rw [Polynomial.coe_mapRingHom]
          repeat rw [Polynomial.map_map]
          -- most terms are useless
          apply congr_fun
          apply congr_arg
          apply RingHom.ext
          intro x
          simp
          -- these two steps are almost the same, but a little hard to generalize
          generalize hsl2: (fun i => Fin.cases Polynomial.X (fun k => Polynomial.C (MvPolynomial.X k)) i: Fin 1 → Polynomial (MvPolynomial (Fin 0) L)) = ls2
          generalize hsk2: (fun i => Fin.cases Polynomial.X (fun k => Polynomial.C (MvPolynomial.X k)) i: Fin 1 → Polynomial (MvPolynomial (Fin 0) K)) = ks2
          have ls2_pass : ls2 = (Polynomial.mapRingHom (MvPolynomial.map (algebraMap K L))) ∘ ks2 := by
            rw [<-hsl2, <-hsk2]
            funext x
            match x with
            | 0 => simp
          rw [ls2_pass]
          rw [commute_C]
          rw [<-MvPolynomial.eval₂_comp_left]
          rw [Polynomial.coe_mapRingHom]
          repeat rw [Polynomial.map_map]
          apply congr_fun
          apply congr_arg
          apply RingHom.ext
          intro x
          simp
          nth_rw 2 [show algebraMap K L = (algebraMap K L).comp (RingHom.id K) from rfl]
          rw [show
            (
              fun i => (algebraMap K L) (Fin.isEmpty'.elim i)
            ) = (algebraMap K L) ∘ (fun (i: Fin 0) => Fin.isEmpty'.elim i) from rfl]
          rw [<-MvPolynomial.eval₂_comp_left]
          simp [MvPolynomial.aeval_def]
          simp [MvPolynomial.eval₂_eq, MvPolynomial.eval_eq]
          apply Finset.sum_congr rfl
          intro x _
          repeat rw [Finset.prod_of_isEmpty]
      -- if roots_x is infinite, we will show that the "resultant" of f and g is zero. The main result is in `coprime_polynomial_polynomial_have_finitely_many_common_roots_1`
      unfold roots_x at roots_x_infinite
      have :
        {
          x | ∃ (k: Fin 2 -> L), Polynomial.evalEval (k 1) (k 0) (algMap (equiv f)) = 0 ∧ Polynomial.evalEval (k 1) (k 0) (algMap (equiv g)) = 0 ∧ k 1 = x
        } =
        {
          x | ∃ (y: L), Polynomial.evalEval x y (algMap (equiv f)) = 0 ∧ Polynomial.evalEval x y (algMap (equiv g)) = 0
        } := by
          ext x
          simp
          constructor
          · rintro ⟨k, ⟨h1, h2, h3⟩⟩
            use k 0
            simp [<-h3, h1, h2]
          · rintro ⟨y, ⟨h1, h2⟩⟩
            use fun i => if i = 0 then y else x
            simp [h1, h2]
      simp [aeval_trans] at roots_x_infinite
      rw [this] at roots_x_infinite
      -- use the theorem to prove the main goal
      have := coprime_polynomial_polynomial_have_finitely_many_common_roots_1 L (equiv f) (equiv g) (coprime_equiv coprime) (f_ne_zero_equiv _) (g_ne_zero_equiv _)
      contradiction

      -- finally, we will prove the wlog, which comes from the symmetry of x and y
      have one_of_is_infinite : roots_x.Infinite ∨ roots_y.Infinite := by
        -- at least one of them is infinite, otherwise f, g only have finitely many common roots
        by_contra h
        simp at h
        have : {k: Fin 2 -> L | MvPolynomial.aeval k f = 0 ∧ MvPolynomial.aeval k g = 0} ⊆
        Set.pi Set.univ (fun (i: Fin 2) => if i = 0 then roots_y else roots_x)
        := by
          apply subset_trans (Set.subset_pi_eval_image Set.univ _)
          rw [Set.pi_subset_pi_iff]
          apply Or.inl
          unfold roots_x roots_y
          intro i
          fin_cases i <;> simp <;> intro a ha1 ha2 <;> use a
        have : {k: Fin 2 -> L | MvPolynomial.aeval k f = 0 ∧ MvPolynomial.aeval k g = 0}.Finite := by
          apply Set.Finite.subset _ this
          apply Set.Finite.pi
          intro i
          fin_cases i <;> simp [h.1, h.2]
        contradiction
      simp [roots_x_infinite] at one_of_is_infinite
      let rename_eq := MvPolynomial.renameEquiv K (Equiv.swap (0: Fin 2) (1: Fin 2))
      let f1 := rename_eq f
      let g1 := rename_eq g
      specialize this f1 g1
        (by unfold f1; rw [(map_eq_zero_iff rename_eq (AlgEquiv.injective rename_eq)).ne]; assumption)
        (by unfold g1; rw [(map_eq_zero_iff rename_eq (AlgEquiv.injective rename_eq)).ne]; assumption)
        (coprime_equiv coprime)
      apply this
      unfold f1 g1 rename_eq
      simp [MvPolynomial.aeval_rename]
      rw [<-Set.preimage_setOf_eq (
        p := fun (k: Fin 2 -> L) => MvPolynomial.aeval k f = 0 ∧ MvPolynomial.aeval k g = 0
      ) (
        f := fun (k: Fin 2 -> L) => k ∘ (Equiv.swap (0: Fin 2) (1: Fin 2))
      )]
      apply Set.Infinite.preimage if_infinite_common_roots
      intro k hk
      simp
      use (k ∘ (Equiv.swap (0: Fin 2) (1: Fin 2)))
      rw [Function.comp_assoc, <-Equiv.coe_trans]
      simp
      unfold roots_y at one_of_is_infinite
      apply Eq.substr (p := fun (s: Set L) => s.Infinite) ?_ one_of_is_infinite -- show x, y are indeex exchanged
      ext x
      simp
      unfold f1 g1 rename_eq
      simp [MvPolynomial.aeval_rename]
      constructor <;> intro h <;> let ⟨k, hk⟩ := h <;> use (k ∘ (Equiv.swap (0: Fin 2) (1: Fin 2))) <;> simp [hk]
      rw [Function.comp_assoc, <-Equiv.coe_trans]
      simp [hk]
