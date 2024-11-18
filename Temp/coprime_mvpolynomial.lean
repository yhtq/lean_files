import Mathlib

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

theorem common_denom_ne_zero {a: Polynomial (RatFunc K)}:
  common_denom a = 0 -> False := by
    intro h
    simp [common_denom] at h
    rw [Finset.prod_eq_zero_iff] at h
    let ⟨i, ⟨hi1, hi2⟩⟩ := h
    have := RatFunc.denom_ne_zero (a.coeff i)
    contradiction

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
      -- if denom = 1, then it equal to its num
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
          constructor <;> intro h
          · use h; apply f_aux_non_zero
            simp [h]
          · exact h.1
      }
    -- show every coefficient is equal
    apply Polynomial.ext
    intro n
    rw [Polynomial.coeff_C_mul]
    simp
    by_cases h: n ∈ a.support <;> simp [h]
    · rw [<-f_aux_eq]
      rw [mul_comm]
      exact h
    · apply Or.inr
      exact Polynomial.not_mem_support_iff.mp h


-- a weak version of the following theorem
theorem coprime_polynomial_polynomial_have_finitely_many_common_roots
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

theorem coprime_ratFunc_of_relPrime (f g: Polynomial (Polynomial K)) (coprime: IsRelPrime f g) : IsCoprime (Polynomial.map (algebraMap (Polynomial K) (RatFunc K)) f) (Polynomial.map (algebraMap (Polynomial K) (RatFunc K)) g) := by
  letI : DecidableEq K := Classical.decEq K
  letI : DecidableEq (RatFunc K) := Classical.decEq _
  rw [<-isRelPrime_iff_isCoprime]
  intro d hd1 hd2
  let common_denom := common_denom d


-- 1. Take the resultant of two polynomial:
--     $$
--     R(x_1) = u(x_1, x_2)f(x_1, x_2) + v(x_1, x_2) g(x_1, x_2)
--     $$
-- 2. if $f, g$ have infinitely many common roots, then $R(x_1) = 0$, $(k[x_1])[x_2]$ is a integral domain gives that $f, g$ have a common divisor, which is absurd.
-- remark: resultant is not implemented in mathlib yet, so we wiil use coprime on $(k(x_1))[x_2]$ (which holds if f and g are primitives, but actually we can just take primPart of them) to get a polynomial close to resultant
-- at the same time, the field extension can cause some trouble because coprime elements could not be coprime in ring extension, but when we consider coprime on $(k(x_1))[x_2]$, field extension keeps coprime.
theorem coprime_mvPolynomial_have_finitely_many_common_roots
    -- actually there is a section "Polynomial.Bivariate" in mathlib, but here I manage to use MvPolynomial and do a muanual transformation
    (L: Type*) [Field L] [Algebra K L]
    (f g: MvPolynomial (Fin 2) K)
    (coprime: IsRelPrime f g)  -- notice that IsCoprime in Mathlib is defined as $(a) + (b) = 1$, however the meaning in the exercise is more close to have no common divisor.
    :
    {k: Fin 2 -> L | MvPolynomial.aeval k f = 0 ∧ MvPolynomial.aeval k g = 0}.Finite := by
      letI : DecidableEq K := Classical.decEq K
      letI : DecidableEq (RatFunc K) := Classical.decEq _
      by_contra if_infinite_common_roots
      -- if the set is finite
      simp [<-Set.not_infinite] at if_infinite_common_roots
      let equiv_2_to_1 := MvPolynomial.finSuccEquiv K 1
      simp at equiv_2_to_1
      let equiv_1_to_0 := MvPolynomial.finSuccEquiv K 0
      simp at equiv_1_to_0
      let equiv_0_to_K := MvPolynomial.isEmptyAlgEquiv K (Fin 0)
      let equiv_1_to_poly := Polynomial.mapAlgEquiv equiv_0_to_K
      -- to construct a K-algebra equiv from MvPolynomial (Fin 2) K to Polynomial (Polynomial K))
      let equiv := (equiv_2_to_1.trans $ Polynomial.mapAlgEquiv equiv_1_to_0).trans $ Polynomial.mapAlgEquiv equiv_1_to_poly
      have equiv_eval (f: MvPolynomial (Fin 2) K): ∀ k: Fin 2 -> K,
        MvPolynomial.eval k f = Polynomial.eval (k 1) (Polynomial.eval (Polynomial.C $ k 0) (equiv f)) := by
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
          unfold equiv equiv_2_to_1 equiv_1_to_0 equiv_1_to_poly equiv_0_to_K
          simp [eval_eq_eval_mv_eval_ringHom, AlgEquiv.coe_trans, Polynomial.eval_map, Polynomial.eval₂_map]
          simp [<-Polynomial.coe_mapRingHom, <-Polynomial.coe_eval₂RingHom]
          repeat rw [<-Polynomial.mapRingHom_comp]
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
      let f' := equiv f
      let g' := equiv g
      -- map Polynomial (Polynomial K) to Polynomial (FractionRing (Polynomial K))
      let frac_Kx := RatFunc K
      let poly_to_rat := algebraMap (Polynomial K) frac_Kx
      let inj_to_frac := Polynomial.mapAlg (Polynomial K) (frac_Kx)
      have : Function.Injective inj_to_frac := by apply Polynomial.map_injective; exact NoZeroSMulDivisors.algebraMap_injective (Polynomial K) frac_Kx
      let f'_frac := inj_to_frac f'
      let g'_frac := inj_to_frac g'
      -- then we can get a f'_frac + b g'_frac = 1. Firstly we prove the situation that f, g is Primitive
      have : f'.IsPrimitive -> g'.IsPrimitive -> IsCoprime f'_frac g'_frac := by
        intro hf' hg'
        rw [<-isRelPrime_iff_isCoprime] -- we will show there is no common divisor
        intro d hd1 hd2
        -- denominate of d
        let common_denom := ∏ i in d.support, (d.coeff i).denom
        have d_nezero : d ≠ 0 := by
          -- if d = 0, then f, g = 0, which is contridct to coprime codition. This will be used very later
          intro h
          rw [h] at hd1 hd2
          simp at hd1 hd2
          unfold f'_frac at hd1
          rw [map_eq_zero_iff _ this] at hd1
          unfold f' at hd1
          rw [map_eq_zero_iff _ (AlgEquiv.injective _)] at hd1
          unfold g'_frac at hd2
          rw [map_eq_zero_iff _ this] at hd2
          unfold g' at hd2
          rw [map_eq_zero_iff _ (AlgEquiv.injective _)] at hd2
          rw [hd1, hd2] at coprime
          apply IsRelPrime.ne_zero_or_ne_zero at coprime
          simp [hd1, hd2] at coprime
        have common_denom_ne_zero : common_denom ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          exact fun a a_1 ↦ RatFunc.denom_ne_zero (d.coeff a)
        -- cancel denominators of d
        have : ∀ i: ℕ , i ∈ d.support -> ∃ d_num: Polynomial K, common_denom * (d.coeff i) = d_num := by
          intro i hi
          have : (d.coeff i).denom ∣ common_denom := by
            unfold common_denom
            exact Finset.dvd_prod_of_mem (fun i ↦ RatFunc.denom (d.coeff i)) hi
          let ⟨p, hp⟩ :=(RatFunc.denom_dvd (common_denom_ne_zero)).mp this
          use p
          rw [hp]
          field_simp [show (algebraMap (Polynomial K) (RatFunc K)) common_denom ≠ 0 from RatFunc.algebraMap_ne_zero common_denom_ne_zero]
          rw [mul_comm]
          rfl
        let hd1 := mul_dvd_mul_left (Polynomial.C common_denom: Polynomial frac_Kx) hd1
        let hd2 := mul_dvd_mul_left (Polynomial.C common_denom: Polynomial frac_Kx) hd2
        have hp : (((Polynomial.C common_denom: Polynomial frac_Kx) * d).coeffs).toSet ⊆ ((Subring.map poly_to_rat ⊤): Set frac_Kx) := by
          -- show the coefficients of d' is in the range of poly_to_rat
            simp
            intro a ha
            let ⟨i, ⟨hi1, hi2⟩⟩ := Polynomial.mem_coeffs_iff.mp ha
            simp at hi2 hi1
            let ⟨d_num, hd_num⟩ := this i (
              by
               simp
               exact hi1.2
            )
            rw [hd_num] at hi2
            rw [hi2]
            simp
            use d_num
            rfl
        -- the result of denominator should be a image of injection. Polynomial.toSubring is really hard to use.
        let _d' := Polynomial.toSubring ((Polynomial.C common_denom: Polynomial frac_Kx) * d) (Subring.map  poly_to_rat ⊤) (
          hp
        )
        let equiv_aux := (Subring.equivMapOfInjective ⊤ poly_to_rat (RatFunc.algebraMap_injective K)).symm.trans ((Subring.topEquiv))
        let d' := Polynomial.map (S := Polynomial K) equiv_aux _d'
        have covert_lemma: Polynomial.map poly_to_rat d' = (Polynomial.C common_denom: Polynomial frac_Kx) * d := by
          unfold d'
          rw [Polynomial.map_map]
          have : poly_to_rat.comp equiv_aux = (Subring.map  poly_to_rat ⊤).subtype := by
            apply RingHom.ext
            intro x
            simp
            unfold equiv_aux
            simp
            rw [<-Subring.coe_equivMapOfInjective_apply]
            simp
            exact RatFunc.algebraMap_injective K
          rw [this]
          unfold _d'
          simp
        rw [<-covert_lemma] at hd1 hd2
        rw [show f'_frac = Polynomial.map poly_to_rat f' from rfl] at hd1
        rw [show g'_frac = Polynomial.map poly_to_rat g' from rfl] at hd2
        have is_unit: IsUnit (Polynomial.C common_denom: Polynomial frac_Kx) := by
          apply Polynomial.isUnit_C.mpr
          simp []
          rw [<-ne_eq]
          show (algebraMap (Polynomial K) (RatFunc K)) common_denom ≠ 0
          exact RatFunc.algebraMap_ne_zero common_denom_ne_zero
        rw [IsUnit.dvd_mul_left is_unit] at hd1 hd2
        -- take the prim part of d'
        let d'_prim := d'.primPart
        have dvd_d' := Polynomial.map_dvd poly_to_rat d'.primPart_dvd
        apply dvd_trans dvd_d' at hd1
        apply dvd_trans dvd_d' at hd2
        -- use the key theorem which pass Polynomial.map (algebraMap R K) p ∣ Polynomial.map (algebraMap R K) q tp p | q, simiarly to Gauss lemma
        rw [<-(Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map _ (Polynomial.isPrimitive_primPart d'))] at hd1 hd2
        <;> (try assumption)
        apply (map_dvd_iff equiv.symm).mpr at hd1
        apply (map_dvd_iff equiv.symm).mpr at hd2
        simp [f', g'] at hd1 hd2
        have := coprime hd1 hd2
        simp at this
        have d'_eq := Polynomial.eq_C_content_mul_primPart d'
        apply_fun (Polynomial.map (equiv_aux.symm: Polynomial K →+* ↥(Subring.map poly_to_rat ⊤)) ) at d'_eq
        simp at d'_eq
        have d'_rev: _d' = Polynomial.map (equiv_aux.symm) d' := by
          unfold d'
          simp [Polynomial.map_map]
        rw [<-d'_rev] at d'_eq
        have isunit__d' := IsUnit.map (Polynomial.mapEquiv (equiv_aux.symm)) this
        rw [Polynomial.mapEquiv_apply] at isunit__d'
        -- unluckily, there are only lemmas about degree to use in toSubring, so we must get IsUnit from degree
        have := Polynomial.degree_toSubring _ _ hp
        have : _d'.degree = ((Polynomial.C common_denom: Polynomial frac_Kx) * d).degree := this
        -- we will use it later
        have this2 := this
        rw [d'_eq] at this
        simp at this
        repeat rw [Polynomial.degree_C] at this
        rw [Polynomial.degree_eq_zero_of_isUnit isunit__d'] at this
        simp at this
        -- degree shows d is unit
        exact Polynomial.isUnit_iff_degree_eq_zero.mpr (id (Eq.symm this))
        -- other trivial conditions
        show (algebraMap (Polynomial K) (RatFunc K)) common_denom ≠ 0
        exact RatFunc.algebraMap_ne_zero common_denom_ne_zero
        -- d'.content finally leads to d = 0, which is impossible
        rw [(RingEquiv.map_eq_zero_iff _).ne]
        rw [Polynomial.content_eq_zero_iff.ne]
        intro hd'
        unfold d' at hd'
        rw [Polynomial.map_eq_zero_iff] at hd'
        rw [hd'] at this2
        -- use degree equation to derive d = 0
        simp only [Polynomial.degree_zero] at this2
        symm at this2
        rw [Polynomial.degree_eq_bot] at this2
        simp at this2
        rcases this2 with h | h
        · have : (algebraMap (Polynomial K) (RatFunc K)) common_denom ≠ 0 := RatFunc.algebraMap_ne_zero common_denom_ne_zero
          exact this h
        · exact d_nezero h
        exact EquivLike.injective equiv_aux
      let roots_x := {x: L | ∃ k: Fin 2 -> L, MvPolynomial.aeval k f = 0 ∧ MvPolynomial.aeval k g = 0 ∧ k 1 = x}
      let roots_y := {y: L | ∃ k: Fin 2 -> L, MvPolynomial.aeval k f = 0 ∧ MvPolynomial.aeval k g = 0 ∧ k 0 = y}
      -- in fact, we can assume roots_x is infinite, otherwise we just exchange x and y in f and g
      have : roots_x.Infinite ∨ roots_y.Infinite := by
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
          fin_cases i <;> simp <;> intro a ha1 ha2 <;> use a <;> simp [ha1, ha2]
        have : {k: Fin 2 -> L | MvPolynomial.aeval k f = 0 ∧ MvPolynomial.aeval k g = 0}.Finite := by
          apply Set.Finite.subset _ this
          apply Set.Finite.pi
          intro i
          fin_cases i <;> simp [h.1, h.2]
        contradiction
