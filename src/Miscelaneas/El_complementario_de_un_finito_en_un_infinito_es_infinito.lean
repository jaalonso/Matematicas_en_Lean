import data.fintype.basic
import data.set.finite

-- Notas:
-- + Un tipo α es finito si hay un número finito de elementos de tipo
--   α. Se denota por `fintype α` y se define por
--      class fintype (α : Type*) :=
--      (elems [] : finset α)
--      (complete : ∀ x : α, x ∈ elems)
--   donde `elems` es una lista finita (sin repeticiones de los
--   elementos de α y `complete`expresa que todos los elementos de tipo
--   α están en `elems`.
-- + Un tipo α es infinito si no es finito. Se denota por `infinite α` y
--   se define por
--      class infinite (α : Type*) : Prop :=
--      (not_fintype : fintype α → false)
-- + `s.finite` indica que el conjunto `s` es finito. La definición de
--    conjunto finito es
--      def finite (s : set α) : Prop := nonempty (fintype s)
-- + `s.infinite` indica que el conjunto `s` es infinito. La definición
--   de conjunto infinito es
--      def infinite (s : set α) : Prop := ¬ finite s
-- + `sᶜ` es el complementario de `s` y está caracterizado por
--      mem_compl_iff (s : set α) (x : α) : x ∈ sᶜ ↔ x ∉ s
-- + El universo de los tipos infinitos son infinitos:
--      infinite_univ [h : _root_.infinite α] : infinite (@univ α)

lemma infinite_of_finite_compl
  {α : Type} [infinite α]
  {s : set α}
  (hs : sᶜ.finite)
  : s.infinite :=
λ h, set.infinite_univ (by simpa using hs.union h)

lemma compl_infinite_of_finite
  {α : Type} [infinite α]
  {s : set α}
  (hs : s.finite)
  : sᶜ.infinite :=
λ h, set.infinite_univ (by simpa using hs.union h)
