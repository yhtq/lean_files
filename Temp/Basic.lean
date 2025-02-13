import Std
import Lean
import Mathlib.Tactic
open Lean


inductive Free (f : Type _ -> Type _) (a: Type _)
| pure : a -> Free f a
| roll : ∀ x, f x -> (x -> Free f a) → Free f a

def bind_aux (x : Free f a) (f1 : a -> Free f b) : Free f b :=
  match x with
  | Free.pure a => f1 a
  | Free.roll _ fx k => Free.roll _ fx (fun x => bind_aux (k x) f1)

lemma bind_rw [Monad f] [LawfulMonad f] {m : f a} {f1 f2 : a -> f b} (h : ∀ x, f1 x = f2 x) : m >>= f1 = m >>= f2 := by
  rw [show f1 = f2 by funext x; apply h]

instance (f : Type -> Type) : Monad (Free f) where
  pure := Free.pure
  bind := bind_aux

lemma bind_def (m : Free f a) (f : a -> Free f b) : m >>= f = bind_aux m f := rfl

instance (f : Type -> Type) : LawfulMonad (Free f) := sorry
instance : LawfulMonad (OptionT (StateM s)) := sorry

abbrev liftF {f : Type -> Type} {a : Type} (fx : f a) : Free f a :=
  Free.roll _ fx Free.pure

inductive IMPValue
| num : Int -> IMPValue
| bool : Bool -> IMPValue

instance : ToExpr IMPValue where
  toExpr
    | IMPValue.num n => mkApp (mkConst `IMPValue.num) (toExpr n)
    | IMPValue.bool b => mkApp (mkConst `IMPValue.bool) (toExpr b)
  toTypeExpr := mkConst `IMPValue

instance : Inhabited IMPValue where
  default := IMPValue.num 0

inductive IMPExp a
| val : IMPValue -> (IMPValue -> a) -> IMPExp a
| add : IMPValue -> IMPValue -> (IMPValue -> a) -> IMPExp a
| lt : IMPValue -> IMPValue -> (IMPValue -> a) -> IMPExp a

instance : Functor IMPExp where
  map f imp :=
    match imp with
      | IMPExp.val v g => IMPExp.val v (fun x => f (g x))
      | IMPExp.add e1 e2 g => IMPExp.add e1 e2 (fun x => f (g x))
      | IMPExp.lt e1 e2 g => IMPExp.lt e1 e2 (fun x => f (g x))

abbrev FreeIMPExp := Free IMPExp

def run_freeIMPExp {a : Type} : FreeIMPExp a -> Option a :=
  fun x => match x with
  | Free.pure a => some a
  | Free.roll _ fx k => match fx with
    | IMPExp.val v f => run_freeIMPExp (k (f v))
    | IMPExp.add e1 e2 f =>
      match e1, e2 with
      | IMPValue.num n1, IMPValue.num n2 => run_freeIMPExp (k (f (IMPValue.num (n1 + n2))))
      | _, _ => none
    | IMPExp.lt e1 e2 f =>
      match e1, e2 with
      | IMPValue.num n1, IMPValue.num n2 => run_freeIMPExp (k (f (IMPValue.bool (n1 < n2))))
      | _, _ => none

abbrev Val := fun (val : IMPValue) => liftF $ IMPExp.val val id
abbrev AddV := fun (e1 e2 : IMPValue) => liftF $ IMPExp.add e1 e2 id
abbrev Lt := fun (e1 e2 : IMPValue) => liftF $ IMPExp.lt e1 e2 id

def test_free_exp : FreeIMPExp IMPValue := do
  let a <- liftF $ IMPExp.val (IMPValue.num 10) id
  let b <- liftF $ IMPExp.val (IMPValue.num 20) id
  liftF $ IMPExp.add a b id


inductive IMP (a : Type)
| skip : a -> IMP a
| assign : (String × IMPValue) -> a -> IMP a
| ifThenElse : IMPValue -> a -> a -> IMP a
| get : String -> (IMPValue -> a) -> IMP a

instance : Functor IMP where
  map f imp :=
    let rec aux (a : Type) (b : Type) (f : a -> b) (imp : IMP a) : IMP b :=
      match imp with
      | IMP.skip a => IMP.skip (f a)
      | IMP.assign x a => IMP.assign x (f a)
      | IMP.ifThenElse cond t e  => IMP.ifThenElse cond (f t) (f e)
      | IMP.get x k => IMP.get x (fun y => f (k y))
    aux _ _ f imp

abbrev FreeIMP := Free IMP
-- FreeIMP 可以看作一个命令式语言程序，而右侧完全是一个 functional program
-- 可以认为后者是前者的一个语义。这个翻译过程和翻译到逻辑命题是非常相似的
-- 虽然后者是 StateM，但如果我们假设命令式程序无上下文也无副作用，实际上就是我们可以从空状态开始 runState
def IMP_to_stateM : FreeIMP a -> OptionT (StateM (RBMap String IMPValue (fun a b => compareOfLessAndEq a b))) a :=
  fun x => match x with
  | Free.pure a => OptionT.pure a
  | Free.roll _ fx k => match fx with
    | IMP.skip a => IMP_to_stateM (k a)
    | IMP.assign (name, val) f => do
      let m ← get
      let m' := m.insert name val
      set m'
      IMP_to_stateM (k f)
    | IMP.ifThenElse cond t e =>
      match cond with
      | IMPValue.bool true => IMP_to_stateM (k t)
      | IMPValue.bool false => IMP_to_stateM (k e)
      | _ => OptionT.fail
    | IMP.get name f => do
      let m ← get
      match m.find? name with
      | some val => IMP_to_stateM (k (f val))
      | none => OptionT.fail

lemma step (m : FreeIMP a) (f : a -> FreeIMP b) : IMP_to_stateM (m >>= f) = IMP_to_stateM m >>= fun x => IMP_to_stateM (f x) := by
  conv =>
    lhs
    rw [bind_def]
    unfold bind_aux
  match m with
  | Free.pure a =>
    simp [IMP_to_stateM]
    rfl
  | Free.roll _ fx k =>
    simp
    conv =>
      lhs
      unfold IMP_to_stateM
      simp [<-bind_def, step]
    conv =>
      rhs
      rw [IMP_to_stateM.eq_def]
      simp
    split <;> try aesop
    sorry

    -- rename _ => f1
    -- conv =>
    --   lhs
    --   rw [show (
    --     (fun (x : a) => OptionT.fail) = do
    --       OptionT.fail
    --       IMP_to_stateM (f x)
    --     ) from rfl
    --   ]

abbrev ifThenElse' {a : Type} [Inhabited a] (cond : FreeIMPExp IMPValue) (t : FreeIMP a) (e : FreeIMP a) : FreeIMP a :=
  let c := run_freeIMPExp cond
  match c with
  | some val => do
    match val with
    | IMPValue.bool true => t
    | IMPValue.bool false => e
    | _ => panic! "ifThenElse' failed"
  | none => panic! "ifThenElse' failed"

abbrev Assign := fun (name : String) (val : IMPValue) => liftF $ IMP.assign (name, val) ()
abbrev Get := fun (name : String) => liftF $ IMP.get name id
abbrev Skip := liftF $ IMP.skip ()

def test_imp : FreeIMP IMPValue := do
  -- liftF $ IMP.assign ("x", IMPValue.num 10) ()
  -- liftF $ IMP.assign ("x", IMPValue.num 20) ()
  -- liftF $ IMP.assign ("y", IMPValue.num 30) ()
  ifThenElse' (Lt (IMPValue.num 10) (IMPValue.num 30)) (Assign "z" $ IMPValue.num 10) (Assign "z" $ IMPValue.num 30)
  let r <- Get "z"
  Skip
  pure r

-- "运行"程序，可以想象结果（的表达式）就是命令式语言的函数式 spec (semantics)
def run_stateM_empty : FreeIMP a -> Option a :=
  fun x => (OptionT.run (IMP_to_stateM x) (RBMap.empty)).1

instance [ToExpr a] : ToExpr (Option a) where
  toExpr := fun
    | some a => mkApp (mkConst `some) (toExpr a)
    | none => mkConst `none
  toTypeExpr  := mkConst `Option

#eval run_stateM_empty test_imp
example : run_stateM_empty test_imp = some (IMPValue.num 10) := by
  unfold run_stateM_empty  test_imp
  repeat rw [step]
  rw [bind_rw step]

  -- simp
