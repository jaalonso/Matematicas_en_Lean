import tactic

variable (Man : Type) 
variable (shaves : Man → Man → Prop)

-- 1ª demostración
example 
  ( h : ∃ x : Man,  ∀ y : Man, shaves x y ↔ ¬ shaves y y )
  : false :=
exists.elim h
( assume barber,
  begin
    intro h,
    have hbarbermpr : ¬shaves barber barber → shaves barber barber,
        from iff.mpr (h barber),
    have hbarbermp  : shaves barber barber → ¬shaves barber barber,
        from iff.mp (h barber),
    have nsbb : ¬shaves barber barber, from
        assume sbb : shaves barber barber,
        show false, from hbarbermp sbb sbb,
    show false, from nsbb (hbarbermpr nsbb)
  end )


-- 2ª demostración
example 
  ( h : ∃ x : Man,  ∀ y : Man, shaves x y ↔ ¬ shaves y y )
  : false :=
exists.elim h
  ( assume barber,
    begin
        intro h2, 
        have hbarber := h2 barber, 
        tauto!, 
    end )

-- 3ª demostración
-- ===============

example : ¬ (∃ x : Man,  ∀ y : Man, shaves x y ↔ ¬ shaves y y ) :=
begin
  rintros ⟨barber, h2⟩,
  have hbarber := h2 barber,
  -- library_search,
  exact (not_iff_self (shaves barber barber)).mp (iff.symm (h2 barber)),
end

-- 4ª demostración
example : ¬ (∃ x : Man,  ∀ y : Man, shaves x y ↔ ¬ shaves y y ) :=
λ ⟨x, hx⟩, (not_iff_self _).1 (hx x).symm

-- 5ª demostración
example
  (h : ∃ x : Man, ∀ y : Man, shaves x y ↔ ¬shaves y y) :
  false :=
exists.elim h $
  assume barber : Man,
  assume h : ∀ y : Man, shaves barber y ↔ ¬shaves y y,
    have hbarber : shaves barber barber ↔ ¬shaves barber barber,
      from h barber,
    have nsbb : ¬shaves barber barber, from
      assume sbb : shaves barber barber,
      show false, from hbarber.mp sbb sbb,
    show false, from nsbb (hbarber.mpr nsbb)

-- 6ª demostración
example 
  ( h : ∃ barber : Man,  ∀ m : Man, shaves barber m ↔ ¬ shaves m m )
  : false :=
begin
  obtain ⟨barber, barber_shaves_only_who_doesnt_self_shave⟩ := h,
  have self_shaving_dilemma := barber_shaves_only_who_doesnt_self_shave barber,
  have dilemma_implies_false := (iff_not_self (shaves barber barber)).mp,
  exact dilemma_implies_false self_shaving_dilemma,
end

