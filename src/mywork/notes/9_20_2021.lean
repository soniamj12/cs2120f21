/-testing if false → false can be proven-/
example : false → false :=
begin
  assume f,
  exact f,
end


/-testing if false → true can be proven-/
example : false → true :=
begin
  assume f,
  exact true.intro,
end

/-testing if true → false can be proven-/
-- example : true → false :=
-- begin
--   assume t,
--   --there are no proofs of false
-- end

example : ¬ false :=
begin
  assume f,
  exact f,
end

example : ¬ 0 = 1 :=
begin
  assume f,
  cases f, -- case analysis on a proposition that cannot be proven
end

example : false → false :=
begin
  assume f,
  cases f,
end

example : false → false :=
begin
  assume f,
  exact false.elim f,
end

-- example : true → true :=
-- begin
--   assume t,
--   cases t,

-- end


theorem false_elim (P : Prop) (f : false) : P :=
begin
  exact false.elim f,
  -- cases f,
end