-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SwitchShows.lean: the kind "the code switch" (K2): WHAT THE
PART SHOWS, SEATED IN A WIDER INPUT AND STATE, AND WHAT ITS SIMULATOR TELLS, ARE ONE TERM
(`coreShows`, Honest/K2/Law/SwitchMoves.lean) AT TWO DATA. Statements with their proofs. A step
toward the statement in Honest/K2/Exact.lean: it says nothing on coins' laws.

  `lift_moves`      the moves of the part as a lift seats it: the two moves, each lifted
  `lifted_shows`    the lifted part, played alone at two rounds from any stand: `coreShows` at the
                    main rows' data that the part's own text makes of the narrowed state
  `sim_tells`       the simulator (`switchSim`, Honest/K2/Sim.lean) at two rounds and two
                    challenges: `coreShows` at what the same text makes of the input of zeros
                    behind the public verdict (`simAsk`): data where the verdict is yes, a refusal
                    where it is no

Limits. The laws speak of two rounds and two challenges alone: these are written into the
statements' terms, as lists of two. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchMoves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.K2.Honest (Sizes)

variable {V W X Xi : Type}

/-- The moves of the part as a lift seats it: the two moves, each lifted. -/
theorem lift_moves (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (carries : List (String × Due)) (see : V → Unit) (wit : W → SwitchAsk) (get : X → Unit)
    (set : X → Unit → X) :
    ((switchPart Sd Z others k carries).lift see wit get set).moves =
      [(moveOne Sd Z others k carries).lift wit get set,
        (moveTwo Sd Z others k carries).lift wit get set] := rfl

/-- **What the lifted part shows**, played alone at two rounds from any stand m, at every coin c and
all carried coins ca: `coreShows` at the data that the part's own text makes of the narrowed state.
-/
theorem lifted_shows (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (carries : List (String × Due)) (see : V → Unit) (wit : W → SwitchAsk) (get : X → Unit)
    (set : X → Unit → X) (nm : String) (ad : Addr) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (v : Option V) (c : Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)))
    (ca : CsAll carries) (x₁ x₂ : Fmt.Drawn) (m : Mid W X) (asks : List (List (List Nat))) :
    (play (((switchPart Sd Z others k carries).lift see wit get set).steps nm ad
        [(d₁, o₁), (d₂, o₂)] v (c, (), ca)) [x₁, x₂] [] m).toOption.map
        (fun y => shownOf y.1 asks) =
      coreShows Sd Z others k d₁ d₂ o₁ o₂ x₁ asks
        (switchRowsAt Z carries ca (m.st.narrow wit get) 0) c := by
  rw [shows_two ((switchPart Sd Z others k carries).lift see wit get set)
    (lift_moves Sd Z others k carries see wit get set) (fun _ _ => rfl) (fun _ _ _ => rfl)]
  exact says_core Sd Z others k carries d₁ d₂ o₁ o₂ x₁ asks c ca ⟨m.seen, m.opened⟩
    (fun a₁ => ⟨m.seen ++ [⟨a₁.vals.map Said.got, x₁⟩], m.opened⟩) (m.st.narrow wit get) _ rfl rfl

/-- **What the simulator tells**, at two rounds and two challenges, at every coin c: `coreShows` at
what the same text makes of the input of zeros behind the public verdict. -/
theorem sim_tells (Sd : Sender) (p : SwitchPlace) (ok : Xi → Bool) (d₁ d₂ : Fmt.DeclaredRound)
    (o₁ o₂ : List Oracle) (x : Xi) (front : Before) (x₁ x₂ : Fmt.Drawn)
    (asks : List (List (List Nat)))
    (c : Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars))) :
    (switchSim Sd p ok [(d₁, o₁), (d₂, o₂)]).tell x front [x₁, x₂] asks c =
      coreShows Sd p.sizes p.others p.foldVars d₁ d₂ o₁ o₂ x₁ asks
        (switchRowsAt p.sizes [] () ⟨simAsk (ok x), [], ()⟩ 0) c := by
  show (play ((switchPart Sd p.sizes p.others p.foldVars []).steps "" ⟨p.place, 0⟩
      [(d₁, o₁), (d₂, o₂)] none (c, (), ())) [x₁, x₂] []
      (Mid.bare ⟨simAsk (ok x), [], ()⟩ [] [])).toOption.map (fun y => shownOf y.1 asks) = _
  rw [shows_two (switchPart Sd p.sizes p.others p.foldVars [])
    (switchPart_moves Sd p.sizes p.others p.foldVars []) (fun _ _ => rfl) (fun _ _ _ => rfl)]
  exact says_core Sd p.sizes p.others p.foldVars [] d₁ d₂ o₁ o₂ x₁ asks c () ⟨[], none⟩
    (fun a₁ => ⟨[] ++ [⟨a₁.vals.map Said.got, x₁⟩], none⟩) ⟨simAsk (ok x), [], ()⟩ _ rfl rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.lift_moves
#print axioms ProofFile.Honest.K2.Law.lifted_shows
#print axioms ProofFile.Honest.K2.Law.sim_tells
