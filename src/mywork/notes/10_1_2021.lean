axioms
(Ball : Type)
(blue : Ball → Prop)
--predicate is a proposition with a parameter
(allBallsBlue: ∀ (b : Ball), blue b)
(tomsBall : Ball)

theorem tomsBallIsBlue : blue tomsBall := 
  allBallsBlue tomsBall











  def ev (n:ℕ) := n % 2 = 0
  def odd (n:ℕ) := n % 2 = 1


  def successor_of_even_is_odd : Prop :=
    ∀ (n : ℕ), ev n → odd (n + 1)
  

--lean assumes that and is right associative