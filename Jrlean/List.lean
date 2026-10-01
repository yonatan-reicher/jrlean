module

namespace List

@[expose]
public section


variable {α β}
variable {l : List α}


instance instMonad : Monad List where
  pure := .singleton
  bind x f := x.flatMap f


attribute [local simp]
  Bind.bind
  Functor.map
  Pure.pure
  Seq.seq
  SeqLeft.seqLeft
  SeqRight.seqRight
  List.singleton


@[simp]
theorem flatMap_singleton_eq_map {f : α → β} : l.flatMap (λ a => [f a]) = l.map f := by
  induction l
  case nil => rfl
  case cons h t ih =>
    rw [List.flatMap_cons]
    rw [ih]
    rw [List.map_cons]
    rw [singleton_append]


instance : LawfulMonad List where
  map_const {α β} := rfl
  id_map x := by simp only [Functor.map, map_id_fun, id_eq]
  seqLeft_eq x y := by
    symm
    show
      ((x.map (Function.const _)).flatMap y.map)
      = (x.flatMap λ a => y.flatMap λ b => [a])
    calc
      _ = (x.flatMap λ a => y.map ((Function.const _) a)) := flatMap_map _ _ _
      _ = (x.flatMap λ a => y.map λ b => a) := by rfl
      _ = (x.flatMap λ a => y.flatMap λ b => [a]) := by
        congr
        funext a
        exact flatMap_singleton_eq_map.symm
  seqRight_eq x y := by
    show x *> y = Function.const _ id <$> x <*> y
    symm
    show
      ((x.map (Function.const _ id)).flatMap λ f => y.map f)
      = (x.flatMap λ a => y)
    calc
      _ = (x.flatMap λ f => y.map ((Function.const _ id) f)) := flatMap_map _ _ _
      _ = (x.flatMap λ a => y.map id) := by rfl
      _ = (x.flatMap λ a => y) := by rw [List.map_id]
  pure_seq g x := by
    simp only [Seq.seq, Functor.map, pure, List.singleton, flatMap_cons, flatMap_nil, append_nil]
  bind_pure_comp f x := by
    show (x.flatMap λ a => [f a]) = x.map f
    exact flatMap_singleton_eq_map
  bind_map x y := by rfl
  pure_bind x f := by
    show [x].flatMap f = f x
    exact flatMap_singleton f x
  bind_assoc x f g := by
    simp only [bind]
    exact flatMap_assoc

instance instAlternative : Alternative List where
  failure := []
  orElse a b := a ++ b ()
