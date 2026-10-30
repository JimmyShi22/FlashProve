-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruRun.lean: an honest prover whose index and stored randomness are
read through two total maps, and its run. runC (Honest/Walk.lean) returns a value in which neither
the index's type nor the randomness's type occurs. So the run of the prover read through is the
run of the prover itself, at the index and the randomness read through: one equation on runs. A
law that reads more than the run crosses by its own law: Honest/ThruStops.lean, Honest/ThruThreads.lean.
At the term g is the identity: a law stated at fullIn does not reach the matrices through this file.

  Prover.thru        the prover read through g on the index and rd on the randomness; the named
                     member of the range is an argument
  Step.thru          a prepared round read through; its move is Move.lift, its stops stay
  Mid.narrow, ChainProgress.narrow   a chain's state, the other way: what the prover's input reads
  RowCoins.thru      a list's coins at the list read through: the same coins
  chainSteps_thru    the rounds of a chain read through are the rounds read through, values and
                     errors alike
  readyTests_thru, ready_thru   the tests and the prepared run
  Ready.ReadThrough, Ready.reads_thru   how two prepared runs stand to each other
  walk_thru          a chain's walk, with the verifier's state beside it
  runC_thru          THE EQUATION
  silentAt_thru, outcomeC_thru   the silent set and the outcome

By what. Part.thru, Placed.thru, Local.thru, Common.thru (Honest/Thru.lean) and ready_ok
(Honest/Law/Run.lean). Part.lift keeps a part's counts, so a part read through is given the same
coins, and the coins need no map but the one that rebuilds a list's tuple.

Limits.
  * The one premise of ready_thru and runC_thru says that the range's test answers alike at the
    two named members. Where both are in range it holds. It cannot be dropped: readyTests asks that
    test first, and a prover read through has a named member of its own.
  * The equation compares the prover read through with the prover. A prover that has been given
    other columns or another key is another prover: Honest/ThruRows.lean treats it.
  * Nothing here says that a run returns, or anything of a measure on coins.
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thru
import Johnson.Desc.ProofFile.Honest.Walk
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {S Cl Xi V V' W W' Y W₀ W₀' Rc Rc' Ky Tr X₀ X : Type}

/-! ## 1 On Except -/

/-- Two results of which the first, read by n, is the second: what follows them agrees if it agrees
at each value. -/
theorem bind_when_read {ε α β γ : Type} {e' : Except ε α} {e : Except ε β} (n : α → β)
    (h : e'.map n = e) {k' : α → Except ε γ} {k : β → Except ε γ} (hk : ∀ a, k' a = k (n a)) :
    e'.bind k' = e.bind k := by
  subst h
  cases e' with
  | error x => rfl
  | ok a => exact hk a

/-- The same for a last step that cannot fail. -/
theorem map_when_read {ε α β γ : Type} {e' : Except ε α} {e : Except ε β} (n : α → β)
    (h : e'.map n = e) {k' : α → γ} {k : β → γ} (hk : ∀ a, k' a = k (n a)) :
    e'.map k' = e.map k := by
  subst h
  cases e' with
  | error x => rfl
  | ok a => exact congrArg Except.ok (hk a)

/-- unfit commutes with a map of the value. -/
theorem unfit_map {α β : Type} (e : Except String α) (f : α → β) :
    unfit (e.map f) = (unfit e).map f := by
  cases e <;> rfl

/-- Three results in a row, each read by a map, and a value made of the three. -/
theorem three_read {ε A A' B B' C C' D D' : Type} (e₁ : Except ε A) (e₂ : Except ε B)
    (e₃ : Except ε C) (f₁ : A → A') (f₂ : B → B') (f₃ : C → C') (k : A → B → C → D)
    (k' : A' → B' → C' → D') (t : D → D')
    (h : ∀ a b c, k' (f₁ a) (f₂ b) (f₃ c) = t (k a b c)) :
    (e₁.map f₁).bind (fun a => (e₂.map f₂).bind fun b => (e₃.map f₃).map fun c => k' a b c) =
      Except.map t (e₁.bind fun a => e₂.bind fun b => e₃.map fun c => k a b c) := by
  cases e₁ with
  | error x => rfl
  | ok a =>
    cases e₂ with
    | error x => rfl
    | ok b =>
      cases e₃ with
      | error x => rfl
      | ok c => exact congrArg Except.ok (h a b c)

/-- A value paired with the values of a result that is read by t. -/
theorem pair_read {ε C R R' : Type} (t : R → R') (e : Except ε C) (l' : Except ε R')
    (l : Except ε R) (h : l' = l.map t) :
    e.bind (fun c => l'.map fun r => (c, r)) =
      Except.map (fun q : C × R => (q.1, t q.2)) (e.bind fun c => l.map fun r => (c, r)) := by
  subst h
  cases e with
  | error x => rfl
  | ok c =>
    cases l with
    | error x => rfl
    | ok r => rfl

/-- A list laid in front of a list that is read by T. -/
theorem append_read {A A' : Type} {T : A → A'} {x' : List A'} {x : List A} (l : List A)
    (h : x' = x.map T) : x' ++ l.map T = (x ++ l).map T := by
  rw [h, List.map_append]

/-- What chainSteps does at a place with a prover's side, in general: the coins, then the later
rounds, then the two laid together. -/
theorem steps_read {C C' A A' : Type} {T : A → A'} (tc : C → C') (e' : Except String C')
    (e : Except String C) (he : e' = e.map tc) (m : String → String) (l' : Except String (List A'))
    (l : Except String (List A)) (hl : l' = l.map (List.map T)) (s' : C' → List A')
    (s : C → List A) (hs : ∀ c, s' (tc c) = (s c).map T) :
    (e'.mapError m).bind (fun c => l'.map fun x => s' c ++ x) =
      Except.map (List.map T) ((e.mapError m).bind fun c => l.map fun x => s c ++ x) := by
  subst he
  subst hl
  cases e with
  | error x => rfl
  | ok c =>
    cases l with
    | error x => rfl
    | ok x => exact congrArg Except.ok (append_read x (hs c))

/-! ## 2 Prepared rounds -/

/-- **A prepared round read through**: its stops and its place stay, its move reads its input by
wit and keeps its own state. -/
def Step.thru (wit : W' → W) (s : Step W Y) : Step W' Y :=
  ⟨s.name, s.addr, s.decl, s.oracles, s.bad, s.hid, s.nth, s.last,
    s.move.map (Move.lift wit id fun _ y => y)⟩

/-- The rounds that Part.steps lays, at moves that are lifted, are the rounds read through. hid' and
len' are what the part read through states: the same as hid and len. -/
theorem zipSteps_thru {C : Type} (wit : W' → W) (name : String) (a : Addr)
    (bad hid' hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (hh : hid' = hid)
    (len' len : Nat) (hl : len' = len) (c : C) (ms : List (Move C W Y)) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (n : Nat),
      ((rs.zip (ms.map (Move.lift wit id fun _ y => y))).zipIdx n).map (fun r =>
        (⟨name, a, r.1.1.1, r.1.1.2, bad, hid', r.2, r.2 + 1 == len',
          some ⟨fun _ => r.1.2.say c, r.1.2.hand⟩⟩ : Step W' Y)) =
      (((rs.zip ms).zipIdx n).map fun r =>
        (⟨name, a, r.1.1.1, r.1.1.2, bad, hid, r.2, r.2 + 1 == len,
          some ⟨fun _ => r.1.2.say c, r.1.2.hand⟩⟩ : Step W Y)).map (Step.thru wit) := by
  subst hh
  subst hl
  induction ms with
  | nil =>
    intro rs n
    cases rs <;> rfl
  | cons m ms ih =>
    intro rs n
    cases rs with
    | nil => rfl
    | cons r rs => exact congrArg (List.cons _) (ih rs (n + 1))

/-- **A part's rounds read through.** Its coins are the part's own. -/
theorem Part.steps_thru (see : V' → V) (wit : W' → W) (p : Part V W Y) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (v' : Option V')
    (hv : v'.map see = v) (c : p.Coins) :
    (p.thru see wit).steps name a rs v' c = (p.steps name a rs v c).map (Step.thru wit) := by
  have hl : (p.thru see wit).moves.length = p.moves.length := by
    show (p.moves.map _).length = p.moves.length
    rw [List.length_map]
  have hh : (fun (f o : List Fmt.Drawn) => v'.bind fun w => (p.thru see wit).hid w f o) =
      (fun (f o : List Fmt.Drawn) => v.bind fun w => p.hid w f o) := by
    subst hv
    cases v' <;> rfl
  exact zipSteps_thru wit name a p.bad _ _ hh _ _ hl c p.moves rs 0

/-- **A list's coins, at the list read through.** The same coins: a part read through takes what
the part takes. -/
def RowCoins.thru (see : V' → V) (wit : W' → W) :
    (ps : List (Part V W Y)) → RowCoins ps → RowCoins (ps.map (Part.thru see wit))
  | [], _ => ()
  | _ :: ps, c => (c.1, RowCoins.thru see wit ps c.2)

/-- A part read through is lent what the part is lent. -/
theorem lendPart_thru (see : V' → V) (wit : W' → W) (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : Addr) (p : Part V W Y) :
    lendPart B rows look a (p.thru see wit) = lendPart B rows look a p := by
  cases p with
  | mk takes spends carries bad hid bS hS moves =>
    simp only [lendPart, Part.thru, Part.lift]
    by_cases h : (takes != dueAt rows a) = true
    · first
        | rw [if_pos h, if_pos h]
        | rw [if_pos h]
    · first
        | rw [if_neg h, if_neg h]
        | rw [if_neg h]
      cases (look a).snd.cut ⟨0, 0⟩ takes <;> rfl

/-- So is a list. -/
theorem lendRow_thru (see : V' → V) (wit : W' → W) (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (a : Place) :
    (ps : List (Part V W Y)) → (j : Nat) →
      lendRow B rows look a (ps.map (Part.thru see wit)) j =
        (lendRow B rows look a ps j).map (RowCoins.thru see wit ps)
  | [], _ => rfl
  | p :: ps, j => by
    have e := lendPart_thru see wit B rows look ⟨a, j⟩ p
    have h := pair_read (RowCoins.thru see wit ps)
      ((lendPart B rows look ⟨a, j⟩ p).mapError fun e => "part " ++ toString j ++ ": " ++ e)
      (lendRow B rows look a (ps.map (Part.thru see wit)) (j + 1))
      (lendRow B rows look a ps (j + 1))
      (lendRow_thru see wit B rows look a ps (j + 1))
    show ((lendPart B rows look ⟨a, j⟩ (p.thru see wit)).mapError
        fun e => "part " ++ toString j ++ ": " ++ e).bind
          (fun c => (lendRow B rows look a (ps.map (Part.thru see wit)) (j + 1)).map
            fun r => (c, r)) = _
    rw [e]
    exact h

/-- A list's rounds read through. -/
theorem rowSteps_thru (see : V' → V) (wit : W' → W) (name : String) (a : Place) (v : Option V)
    (v' : Option V') (hv : v'.map see = v) :
    (ps : List (Part V W Y)) → (j : Nat) → (rs : List (Fmt.DeclaredRound × List Oracle)) →
      (c : RowCoins ps) →
      rowSteps name a v' (ps.map (Part.thru see wit)) j rs (RowCoins.thru see wit ps c) =
        (rowSteps name a v ps j rs c).map (Step.thru wit)
  | [], _, _, _ => rfl
  | p :: ps, j, rs, c => by
    have hl : (p.thru see wit).moves.length = p.moves.length := by
      show (p.moves.map _).length = p.moves.length
      rw [List.length_map]
    have h1 := Part.steps_thru see wit p name ⟨a, j⟩ (rs.take p.moves.length) v v' hv c.1
    have h2 := rowSteps_thru see wit name a v v' hv ps (j + 1) (rs.drop p.moves.length) c.2
    show (p.thru see wit).steps name ⟨a, j⟩ (rs.take (p.thru see wit).moves.length) v' c.1 ++
        rowSteps name a v' (ps.map (Part.thru see wit)) (j + 1)
          (rs.drop (p.thru see wit).moves.length) (RowCoins.thru see wit ps c.2) =
      (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
        rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2).map (Step.thru wit)
    rw [hl, List.map_append, h1, h2]

/-- A side's rounds read through. -/
theorem Placed.steps_thru (see : V' → V) (wit : W' → W) (h : Placed V W Y) (b : Block S Cl)
    (v : Option V) (v' : Option V') (hv : v'.map see = v) (c : RowCoins h.parts) :
    (h.thru see wit).steps b v' (RowCoins.thru see wit h.parts c) =
      (h.steps b v c).map (Step.thru wit) :=
  rowSteps_thru see wit b.name b.place v v' hv h.parts 0 (b.rounds.zip b.oracles) c

/-- A side read through has the side's number of rounds. -/
theorem Placed.rounds_thru (see : V' → V) (wit : W' → W) (g : Placed V W Y) :
    (g.thru see wit).rounds = g.rounds := by
  unfold Placed.rounds
  show (g.parts.map (Part.thru see wit)).foldl (fun (n : Nat) p => n + p.moves.length) 0 = _
  rw [List.foldl_map]
  congr 1
  funext n p
  show n + (p.moves.map _).length = n + p.moves.length
  rw [List.length_map]

/-- And its parts the parts' numbers of moves. -/
theorem Placed.cuts_thru (see : V' → V) (wit : W' → W) (g : Placed V W Y) :
    (g.thru see wit).parts.map (·.moves.length) = g.parts.map (·.moves.length) := by
  show (g.parts.map (Part.thru see wit)).map (·.moves.length) = _
  rw [List.map_map]
  congr 1
  funext p
  show (p.moves.map _).length = p.moves.length
  rw [List.length_map]

/-- And as many parts. -/
theorem Placed.parts_thru (see : V' → V) (wit : W' → W) (g : Placed V W Y) :
    (g.thru see wit).parts.length = g.parts.length := by
  show (g.parts.map (Part.thru see wit)).length = g.parts.length
  rw [List.length_map]

/-- The rounds at a place without a side do not read the side's input. -/
theorem idleSteps_thru (wit : W' → W) (b : Block S Cl) :
    (b.rounds.zip b.oracles).map (fun r =>
        (⟨b.name, ⟨b.place, 0⟩, r.1, r.2, fun _ _ => none, fun _ _ => none, 0, false, none⟩ :
          Step W' Y)) =
      ((b.rounds.zip b.oracles).map fun r =>
        (⟨b.name, ⟨b.place, 0⟩, r.1, r.2, fun _ _ => none, fun _ _ => none, 0, false, none⟩ :
          Step W Y)).map (Step.thru wit) := by
  rw [List.map_map]
  rfl

/-- **A chain's rounds read through**: the same error, or the rounds read through. v and v' are what
the stops are handed. -/
theorem chainSteps_thru (see : V' → V) (wit : W' → W) (B : ProverCoinCounts) (rows : List (Addr × Due))
    (look : Addr → (d : Due) × Cs d) (v : Option V) (v' : Option V') (hv : v'.map see = v)
    (bs : List (Block S Cl)) (hs : List (Placed V W Y)) :
    chainSteps B rows look v' bs (hs.map (Placed.thru see wit)) =
      (chainSteps B rows look v bs hs).map (List.map (Step.thru wit)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hfind : ((hs.map (Placed.thru see wit)).find? fun h => h.place == b.place) =
        (hs.find? fun h => h.place == b.place).map (Placed.thru see wit) := by
      rw [List.find?_map]
      rfl
    rw [chainSteps, chainSteps, hfind]
    by_cases h0 : (b.oracles.length != b.rounds.length) = true
    · rw [if_pos h0, if_pos h0]
      try rfl
    · rw [if_neg h0, if_neg h0]
      cases hs.find? fun h => h.place == b.place with
      | none =>
        show Except.map _ (chainSteps B rows look v' bs (hs.map (Placed.thru see wit))) =
          Except.map _ (Except.map _ (chainSteps B rows look v bs hs))
        rw [ih]
        cases chainSteps B rows look v bs hs with
        | error e => rfl
        | ok l => exact congrArg Except.ok (append_read l (idleSteps_thru wit b))
      | some g =>
        show (if (g.thru see wit).rounds != b.rounds.length then _ else _) =
          Except.map _ (if g.rounds != b.rounds.length then _ else _)
        rw [Placed.rounds_thru, Placed.cuts_thru, Placed.parts_thru]
        split
        · try rfl
        split
        · try rfl
        split
        · try rfl
        split
        · try rfl
        exact steps_read (RowCoins.thru see wit g.parts) _ _
          (lendRow_thru see wit B rows look b.place g.parts 0) _ _ _ ih _ _
          fun c => Placed.steps_thru see wit g b v v' hv c

/-! ## 3 The tests and the prepared run -/

section
variable {S' Cl' V₁ V₂ W₁ W₂ Y₁ : Type} (f : Placed V₂ W₂ Y₁ → Placed V₁ W₁ Y₁)
  (hf : ∀ g, (f g).place = g.place)
include hf

/-- strays reads of the sides their places alone. -/
theorem strays_keep_places (bs : List (Block S' Cl')) (hs : List (Placed V₂ W₂ Y₁)) :
    strays bs (hs.map f) = strays bs hs := by
  unfold strays
  rw [List.filter_map, List.map_map]
  simp only [Function.comp_def, hf]

/-- So does twice. -/
theorem twice_keep_places (hs : List (Placed V₂ W₂ Y₁)) : twice (hs.map f) = twice hs := by
  unfold twice
  simp only [List.filter_map, List.map_map, List.length_map, Function.comp_def, hf]

end

/-- Sides read through stand twice where the sides do. -/
theorem twice_thru (see : V' → V) (wit : W' → W) (hs : List (Placed V W Y)) :
    twice (hs.map (Placed.thru see wit)) = twice hs :=
  twice_keep_places (Placed.thru see wit) (fun _ => rfl) hs

/-- **The prover read through**: g on the index, rd on the stored tables' pads and encoding
randomness. d is the named member of its range. Its key is the prover's, and meet reads the shared
chain's input through the two maps. -/
def Prover.thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (H : Prover W₀ Rc Xi Ky Tr X₀ X) :
    Prover W₀' Rc' Xi Ky Tr X₀ X :=
  { stored := fun w rc => H.stored (g w) (rd rc)
    trace := fun w => H.trace (g w)
    key := H.key
    inRange := fun w => H.inRange (g w)
    dummy := d
    own₀ := H.own₀
    ownShared₀ := H.ownShared₀
    first := H.first.map (Placed.thru (Local.thru g rd) (Local.thru g rd))
    shared := H.shared.map (Placed.thru id (Common.thru g rd))
    second := H.second.map (Placed.thru (Local.thru g rd) (Local.thru g rd))
    meet := fun x t => H.meet x (t.narrow (Common.thru g rd) id) }

/-- **The tests of a run read through** are those of the prover at the index read through, where
the range's test answers alike at the two named members. -/
theorem readyTests_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀')
    (hd : H.inRange (g d) = H.inRange H.dummy) :
    readyTests F B (H.thru g rd d) w = readyTests F B H (g w) := by
  have s1 : strays F.first.blocksInOrder (H.thru g rd d).first = strays F.first.blocksInOrder H.first :=
    strays_keep_places (Placed.thru (Local.thru g rd) (Local.thru g rd)) (fun _ => rfl) _ _
  have s2 : strays F.shared.blocksInOrder (H.thru g rd d).shared = strays F.shared.blocksInOrder H.shared :=
    strays_keep_places (Placed.thru id (Common.thru g rd)) (fun _ => rfl) _ _
  have s3 : strays F.second.blocksInOrder (H.thru g rd d).second = strays F.second.blocksInOrder H.second :=
    strays_keep_places (Placed.thru (Local.thru g rd) (Local.thru g rd)) (fun _ => rfl) _ _
  have t1 : twice (H.thru g rd d).first = twice H.first :=
    twice_keep_places (Placed.thru (Local.thru g rd) (Local.thru g rd)) (fun _ => rfl) _
  have t2 : twice (H.thru g rd d).shared = twice H.shared :=
    twice_keep_places (Placed.thru id (Common.thru g rd)) (fun _ => rfl) _
  have t3 : twice (H.thru g rd d).second = twice H.second :=
    twice_keep_places (Placed.thru (Local.thru g rd) (Local.thru g rd)) (fun _ => rfl) _
  have r1 : (H.thru g rd d).inRange (H.thru g rd d).dummy = H.inRange H.dummy := hd
  have r2 : (H.thru g rd d).inRange w = H.inRange (g w) := rfl
  unfold readyTests
  rw [s1, s2, s3, t1, t2, t3, r1, r2]

/-- What ready does behind its tests, at a trace. -/
def readyWith (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) (tr : Tr) : Except Refusal (Ready W₀ Rc Xi Ky Tr X₀ X) :=
  (unfit (chainSteps B (B.rowsOf 0) (c.look 0)
    (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder H.first)).bind fun m₁ =>
  (sharedSteps F B H ⟨w₀, rc, H.key x⟩ c.shared).bind fun m₂ =>
  (unfit (chainSteps B (B.rowsOf 2) (c.look 2)
    (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second)).map fun m₃ =>
    ⟨⟨w₀, rc, x, tr⟩, ⟨w₀, rc, H.key x⟩, m₁, m₂, m₃⟩

/-- What ready does behind its tests. -/
def readyAfter (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) : Except Refusal (Ready W₀ Rc Xi Ky Tr X₀ X) :=
  match H.trace w₀ x with
  | none => .error ⟨.noTrace, "the request has no trace"⟩
  | some tr => readyWith F B H w₀ rc x c tr

/-- ready is its tests and what follows them. -/
theorem ready_eq (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) :
    ready F B H w₀ rc x c =
      (readyTests F B H w₀).bind fun _ => readyAfter F B H w₀ rc x c := rfl

/-- **A prepared run read through**, at the index and randomness that it is read from. -/
def Ready.thru (g : W₀' → W₀) (rd : Rc' → Rc) (w : W₀') (rc : Rc')
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) : Ready W₀' Rc' Xi Ky Tr X₀ X :=
  ⟨⟨w, rc, R.own.x, R.own.trace⟩, ⟨w, rc, R.common.key⟩,
    R.first.map (Step.thru (Local.thru g rd)), R.shared.map (Step.thru (Common.thru g rd)),
    R.second.map (Step.thru (Local.thru g rd))⟩

/-- The shared chain's rounds read through. -/
theorem sharedSteps_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : Common W₀' Rc' Ky) (c₀ : Purse B.shared) :
    sharedSteps F B (H.thru g rd d) w c₀ =
      (sharedSteps F B H (Common.thru g rd w) c₀).map (List.map (Step.thru (Common.thru g rd))) := by
  show unfit (chainSteps B (B.rowsOf 1) (sharedLook B c₀) (Face.shared.sees w) F.shared.blocksInOrder
      (H.shared.map (Placed.thru id (Common.thru g rd)))) =
    Except.map (List.map (Step.thru (Common.thru g rd)))
      (unfit (chainSteps B (B.rowsOf 1) (sharedLook B c₀)
        (Face.shared.sees (Common.thru g rd w)) F.shared.blocksInOrder H.shared))
  rw [← unfit_map]
  exact congrArg unfit (chainSteps_thru id (Common.thru g rd) B (B.rowsOf 1) (sharedLook B c₀)
    none none rfl F.shared.blocksInOrder H.shared)

/-- Behind the tests, at one trace. -/
theorem readyWith_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (c : Coins B) (tr : Tr) :
    readyWith F B (H.thru g rd d) w rc x c tr =
      (readyWith F B H (g w) (rd rc) x c tr).map (Ready.thru g rd w rc) := by
  have h1 : unfit (chainSteps B (B.rowsOf 0) (c.look 0)
        (Face.own.sees (⟨w, rc, x, tr⟩ : Local W₀' Rc' Xi Tr)) F.first.blocksInOrder (H.thru g rd d).first) =
      (unfit (chainSteps B (B.rowsOf 0) (c.look 0)
        (Face.own.sees (⟨g w, rd rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder H.first)).map
        (List.map (Step.thru (Local.thru g rd))) := by
    rw [← unfit_map]
    exact congrArg unfit (chainSteps_thru (Local.thru g rd) (Local.thru g rd) B (B.rowsOf 0)
      (c.look 0) (Face.own.sees (⟨g w, rd rc, x, tr⟩ : Local W₀ Rc Xi Tr))
      (Face.own.sees (⟨w, rc, x, tr⟩ : Local W₀' Rc' Xi Tr)) rfl F.first.blocksInOrder H.first)
  have h2 : sharedSteps F B (H.thru g rd d) ⟨w, rc, (H.thru g rd d).key x⟩ c.shared =
      (sharedSteps F B H ⟨g w, rd rc, H.key x⟩ c.shared).map
        (List.map (Step.thru (Common.thru g rd))) :=
    sharedSteps_thru g rd d F B H ⟨w, rc, H.key x⟩ c.shared
  have h3 : unfit (chainSteps B (B.rowsOf 2) (c.look 2)
        (Face.own.sees (⟨w, rc, x, tr⟩ : Local W₀' Rc' Xi Tr)) F.second.blocksInOrder
        (H.thru g rd d).second) =
      (unfit (chainSteps B (B.rowsOf 2) (c.look 2)
        (Face.own.sees (⟨g w, rd rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second)).map
        (List.map (Step.thru (Local.thru g rd))) := by
    rw [← unfit_map]
    exact congrArg unfit (chainSteps_thru (Local.thru g rd) (Local.thru g rd) B (B.rowsOf 2)
      (c.look 2) (Face.own.sees (⟨g w, rd rc, x, tr⟩ : Local W₀ Rc Xi Tr))
      (Face.own.sees (⟨w, rc, x, tr⟩ : Local W₀' Rc' Xi Tr)) rfl F.second.blocksInOrder H.second)
  unfold readyWith
  rw [h1, h2, h3]
  exact three_read _ _ _ _ _ _ _ _ _ fun _ _ _ => rfl

/-- Behind the tests. -/
theorem readyAfter_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (c : Coins B) :
    readyAfter F B (H.thru g rd d) w rc x c =
      (readyAfter F B H (g w) (rd rc) x c).map (Ready.thru g rd w rc) := by
  have e : (H.thru g rd d).trace w x = H.trace (g w) x := rfl
  unfold readyAfter
  rw [e]
  cases H.trace (g w) x with
  | none => rfl
  | some tr => exact readyWith_thru g rd d F B H w rc x c tr

/-- **ready at the prover read through**: the same refusal, or the prepared run read through. The
value is compared, not the refusals alone: the run behind it reads the value. -/
theorem ready_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (c : Coins B)
    (hd : H.inRange (g d) = H.inRange H.dummy) :
    ready F B (H.thru g rd d) w rc x c =
      (ready F B H (g w) (rd rc) x c).map (Ready.thru g rd w rc) := by
  rw [ready_eq, ready_eq, readyTests_thru g rd d F B H w hd]
  cases readyTests F B H (g w) with
  | error e => rfl
  | ok u => exact readyAfter_thru g rd d F B H w rc x c

/-- **How a prepared run stands to a prepared run that it reads**: its inputs read through are the
other's, and its rounds are the other's read through. -/
structure Ready.ReadThrough (g : W₀' → W₀) (rd : Rc' → Rc) (R' : Ready W₀' Rc' Xi Ky Tr X₀ X)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) : Prop where
  own : Local.thru g rd R'.own = R.own
  common : Common.thru g rd R'.common = R.common
  first : R'.first = R.first.map (Step.thru (Local.thru g rd))
  shared : R'.shared = R.shared.map (Step.thru (Common.thru g rd))
  second : R'.second = R.second.map (Step.thru (Local.thru g rd))

/-- What ready returns at the index and randomness read through stands so to its image. -/
theorem Ready.reads_thru (g : W₀' → W₀) (rd : Rc' → Rc) {F : FileDescription Xi} {B : ProverCoinCounts}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w : W₀'} {rc : Rc'} {x : Xi} {c : Coins B}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (h : ready F B H (g w) (rd rc) x c = .ok R) :
    Ready.ReadThrough g rd (Ready.thru g rd w rc R) R := by
  obtain ⟨-, tr, -, ho, hc, -⟩ := ready_ok h
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · show (⟨g w, rd rc, R.own.x, R.own.trace⟩ : Local W₀ Rc Xi Tr) = R.own
    rw [ho]
  · show (⟨g w, rd rc, R.common.key⟩ : Common W₀ Rc Ky) = R.common
    rw [hc]

/-! ## 4 A chain's walk -/

/-- **A state of a chain's run, as the prover's side reads it**: the input by wit. -/
def Mid.narrow (wit : W' → W) (m : Mid W' Y) : Mid W Y :=
  ⟨m.st.narrow wit id, m.loc, m.seen, m.opened⟩

/-- **A walk, as the prover's side reads it**: all but the run's state is free of the input. -/
def ChainProgress.narrow (wit : W' → W) (z : ChainProgress S Cl W' Y) : ChainProgress S Cl W Y :=
  ⟨z.mid.map (Mid.narrow wit), z.ver, z.refused, z.laid, z.reads, z.cols, z.todo, z.own⟩

/-- A round's message, read through. -/
theorem Step.tell_thru (wit : W' → W) (s : Step W Y) (back : Option Fmt.RoundView) (m : Mid W' Y) :
    (s.thru wit).tell back m = s.tell back (m.narrow wit) := by
  obtain ⟨name, addr, decl, oracles, bad, hid, nth, last, move⟩ := s
  cases move with
  | none => rfl
  | some mv => rfl

/-- A result that waits on a test of stops, read by n. -/
theorem stops_read {A A' : Type} (n : A → A') (q : Option Refusal) (a : A) (b : A') (h : n a = b) :
    Except.map n (match q with
      | some e => (.error e : Except Refusal A)
      | none => .ok a) =
    (match q with
      | some e => (.error e : Except Refusal A')
      | none => .ok b) := by
  subst h
  cases q <;> rfl

/-- After a round's challenge, read through. -/
theorem Step.hear_thru (wit : W' → W) (s : Step W Y) (x : Told) (d : Fmt.Drawn) (m : Mid W' Y) :
    ((s.thru wit).hear x d m).map (Mid.narrow wit) = s.hear x d (m.narrow wit) := by
  obtain ⟨name, addr, decl, oracles, bad, hid, nth, last, move⟩ := s
  cases move with
  | none => rfl
  | some mv =>
    exact stops_read (Mid.narrow wit)
      (if last = true then
        Step.stop (⟨name, addr, decl, oracles, bad, hid, nth, last, some mv⟩ : Step W Y)
          (m.loc ++ [d]) (nth + 1)
      else none) _ _ rfl

/-- What a sub-protocol reads when it is asked. -/
def settleReads (L : Lay) (b : Block S Cl) (z : ChainProgress S Cl W Y) : List Read :=
  readsOf L.chain L.firstTree L.stored (L.tree z.laid) b.rounds (z.own.map (·.drawn))

/-- The verifier's state after it. -/
def settleVer (L : Lay) (b : Block S Cl) (z : ChainProgress S Cl W Y) (cols : List OpenedColumn) : Option S :=
  z.ver.bind fun s => judge L.firstTree b s (roundsOf z.own) cols

/-- The walk after it. -/
def settleNext (L : Lay) (b : Block S Cl) (z : ChainProgress S Cl W Y) (cols : List OpenedColumn) :
    ChainProgress S Cl W Y :=
  { z with
    ver := settleVer L b z cols
    mid := if (settleVer L b z cols).isSome then z.mid.map (·.took cols) else none
    refused := z.refused.or
      (if z.ver.isSome && (settleVer L b z cols).isNone then some b.place else none)
    reads := z.reads ++ settleReads L b z
    cols := z.cols ++ cols
    own := [] }

/-- ChainProgress.settle where the sub-protocol's rounds are not all produced. -/
theorem settleAt_wait (L : Lay) (b : Block S Cl) (bs : List (Block S Cl)) (z : ChainProgress S Cl W Y)
    (h : z.own.length < b.rounds.length) :
    ChainProgress.settle L (b :: bs) z = .ok { z with todo := b :: bs } := by
  rw [ChainProgress.settle]
  exact if_pos h

/-- ChainProgress.settle where they are. -/
theorem settleAt_go (L : Lay) (b : Block S Cl) (bs : List (Block S Cl)) (z : ChainProgress S Cl W Y)
    (h : ¬ z.own.length < b.rounds.length) :
    ChainProgress.settle L (b :: bs) z =
      (unfit (fillCols (settleReads L b z) [])).bind fun cols =>
        ChainProgress.settle L bs (settleNext L b z cols) := by
  rw [ChainProgress.settle]
  exact if_neg h

/-- Columns laid behind, read through. -/
theorem took_read (wit : W' → W) (c : Bool) (m : Option (Mid W' Y)) (cols : List OpenedColumn) :
    Option.map (Mid.narrow wit) (if c = true then m.map (·.took cols) else none) =
      if c = true then (m.map (Mid.narrow wit)).map (·.took cols) else none := by
  cases c <;> cases m <;> rfl

/-- The walk after a sub-protocol, read through. -/
theorem settleNext_narrow (wit : W' → W) (L : Lay) (b : Block S Cl) (z : ChainProgress S Cl W' Y)
    (cols : List OpenedColumn) :
    ChainProgress.narrow wit (settleNext L b z cols) = settleNext L b (ChainProgress.narrow wit z) cols :=
  congrArg (fun M : Option (Mid W Y) =>
      ({ settleNext L b (ChainProgress.narrow wit z) cols with mid := M } : ChainProgress S Cl W Y))
    (took_read wit (settleVer L b z cols).isSome z.mid cols)

/-- **Settling reads nothing of the input.** -/
theorem ChainProgress.settle_narrow (wit : W' → W) (L : Lay) (bs : List (Block S Cl)) :
    ∀ z : ChainProgress S Cl W' Y,
      (ChainProgress.settle L bs z).map (ChainProgress.narrow wit) = ChainProgress.settle L bs (ChainProgress.narrow wit z) := by
  induction bs with
  | nil =>
    intro z
    rfl
  | cons b bs ih =>
    intro z
    by_cases h : z.own.length < b.rounds.length
    · rw [settleAt_wait L b bs z h, settleAt_wait L b bs (ChainProgress.narrow wit z) h]
      rfl
    · rw [settleAt_go L b bs z h, settleAt_go L b bs (ChainProgress.narrow wit z) h]
      have hq : settleReads L b (ChainProgress.narrow wit z) = settleReads L b z := rfl
      rw [hq]
      cases unfit (fillCols (settleReads L b z) []) with
      | error e => rfl
      | ok cols =>
        show Except.map (ChainProgress.narrow wit) (ChainProgress.settle L bs (settleNext L b z cols)) =
          ChainProgress.settle L bs (settleNext L b (ChainProgress.narrow wit z) cols)
        rw [ih, settleNext_narrow]

/-- A chain's start, read through. -/
theorem ChainProgress.start_narrow (wit : W' → W) (L : Lay) (bs : List (Block S Cl))
    (m : Option (Mid W' Y)) (v : Option S) (front : List OpenedColumn) :
    (ChainProgress.start L bs m v front).map (ChainProgress.narrow wit) =
      ChainProgress.start L bs (m.map (Mid.narrow wit)) v front := by
  cases m <;> cases v <;> exact ChainProgress.settle_narrow wit L bs _

/-- The same, at a state given by its image. -/
theorem ChainProgress.start_of_narrow (wit : W' → W) (L : Lay) (bs : List (Block S Cl))
    {m' : Option (Mid W' Y)} {m : Option (Mid W Y)} (hm : m'.map (Mid.narrow wit) = m)
    (v : Option S) (front : List OpenedColumn) :
    (ChainProgress.start L bs m' v front).map (ChainProgress.narrow wit) = ChainProgress.start L bs m v front := by
  subst hm
  exact ChainProgress.start_narrow wit L bs m' v front

/-- A round's message in a walk, read through. -/
theorem ChainProgress.say_thru (wit : W' → W) (z : ChainProgress S Cl W' Y) (s : Step W Y) :
    z.say (s.thru wit) = (ChainProgress.narrow wit z).say s := by
  obtain ⟨mid, ver, refused, laid, reads, cols, todo, own⟩ := z
  cases mid with
  | none => rfl
  | some m => exact Step.tell_thru wit s none m

/-- After a round's challenge in a walk, read through. -/
theorem ChainProgress.heard_thru (wit : W' → W) (L : Lay) (z : ChainProgress S Cl W' Y) (s : Step W Y) (x : Told)
    (d : Fmt.Drawn) :
    (z.heard L (s.thru wit) x d).map (ChainProgress.narrow wit) = (ChainProgress.narrow wit z).heard L s x d := by
  obtain ⟨mid, ver, refused, laid, reads, cols, todo, own⟩ := z
  cases mid with
  | none => exact ChainProgress.settle_narrow wit L todo _
  | some m =>
    have h := Step.hear_thru wit s x d m
    show Except.map (ChainProgress.narrow wit) ((((s.thru wit).hear x d m).map some).bind _) =
      ((s.hear x d (m.narrow wit)).map some).bind _
    rw [← h]
    cases (s.thru wit).hear x d m with
    | error e => rfl
    | ok m' => exact ChainProgress.settle_narrow wit L todo _

/-- **A chain's walk read through.** -/
theorem walk_thru (wit : W' → W) (L : Lay) (ss : List (Step W Y)) :
    ∀ (ds : List Fmt.Drawn) (z : ChainProgress S Cl W' Y),
      (walk L (ss.map (Step.thru wit)) ds z).map (ChainProgress.narrow wit) =
        walk L ss ds (ChainProgress.narrow wit z) := by
  induction ss with
  | nil =>
    intro ds z
    cases ds <;> rfl
  | cons s ss ih =>
    intro ds z
    cases ds with
    | nil => rfl
    | cons d ds =>
      show Except.map (ChainProgress.narrow wit) ((z.say (s.thru wit)).bind fun x =>
                   (z.heard L (s.thru wit) x d).bind fun z' => walk L (ss.map (Step.thru wit)) ds z') =
        ((ChainProgress.narrow wit z).say s).bind fun x =>
          ((ChainProgress.narrow wit z).heard L s x d).bind fun z' => walk L ss ds z'
      rw [ChainProgress.say_thru]
      cases (ChainProgress.narrow wit z).say s with
      | error e => rfl
      | ok x =>
        show Except.map (ChainProgress.narrow wit) ((z.heard L (s.thru wit) x d).bind fun z' =>
                     walk L (ss.map (Step.thru wit)) ds z') =
          ((ChainProgress.narrow wit z).heard L s x d).bind fun z' => walk L ss ds z'
        rw [← ChainProgress.heard_thru wit L z s x d]
        cases z.heard L (s.thru wit) x d with
        | error e => rfl
        | ok z' => exact ih ds z'

/-- The same at rounds given by their image. -/
theorem walk_of_thru (wit : W' → W) (L : Lay) {ss' : List (Step W' Y)} {ss : List (Step W Y)}
    (h : ss' = ss.map (Step.thru wit)) (ds : List Fmt.Drawn) (z : ChainProgress S Cl W' Y) :
    (walk L ss' ds z).map (ChainProgress.narrow wit) = walk L ss ds (ChainProgress.narrow wit z) := by
  subst h
  exact walk_thru wit L ss ds z

/-! ## 5 A file -/

/-- The three chains' starts, read through. -/
theorem Ready.start₁_narrow (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀')
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) {R' : Ready W₀' Rc' Xi Ky Tr X₀ X}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (h : Ready.ReadThrough g rd R' R) :
    Mid.narrow (Local.thru g rd) (R'.start₁ (H.thru g rd d)) = R.start₁ H := by
  obtain ⟨own, common, f, s, t⟩ := R
  have ho : Local.thru g rd R'.own = own := h.own
  subst ho
  rfl

theorem Ready.start₂_narrow (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀')
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) {R' : Ready W₀' Rc' Xi Ky Tr X₀ X}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (h : Ready.ReadThrough g rd R' R) :
    Mid.narrow (Common.thru g rd) (R'.start₂ (H.thru g rd d)) = R.start₂ H := by
  obtain ⟨own, common, f, s, t⟩ := R
  have hc : Common.thru g rd R'.common = common := h.common
  subst hc
  rfl

theorem Ready.start₃_narrow (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀')
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) {R' : Ready W₀' Rc' Xi Ky Tr X₀ X}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (h : Ready.ReadThrough g rd R' R)
    (m₁ : Mid (Local W₀' Rc' Xi Tr) X) (m₂ : Mid (Common W₀' Rc' Ky) X₀) :
    Mid.narrow (Local.thru g rd) (R'.start₃ (H.thru g rd d) m₁ m₂) =
      R.start₃ H (Mid.narrow (Local.thru g rd) m₁) (Mid.narrow (Common.thru g rd) m₂) := by
  obtain ⟨own, common, f, s, t⟩ := R
  have ho : Local.thru g rd R'.own = own := h.own
  subst ho
  rfl

/-- **What runC does behind ready.** The columns are an argument: nothing here reads the stored
table otherwise. -/
def runFromReady (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (stored : Nat → Nat → Option (List UInt64)) (x : Xi) (ρ : Draws)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) : Except Refusal (RunC F) :=
  (ChainProgress.start ⟨0, 0, stored, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
    (some (F.start₁ (F.pub x))) []).bind fun a₁ =>
  (walk ⟨0, 0, stored, treeOwn⟩ R.first ρ.first a₁).bind fun z₁ =>
  if !sealQuiet z₁.laid then .error ⟨.unfit, "the sealing round sends or draws something"⟩ else
  (ChainProgress.start ⟨1, 0, stored, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
    (some (F.start₂ (F.pub x))) []).bind fun a₂ =>
  (walk ⟨1, 0, stored, treeOwn⟩ R.shared ρ.shared a₂).bind fun z₂ =>
  (ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, stored, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
    (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
    (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)).bind fun a₃ =>
  (walk ⟨2, F.lastChainFirstTreeNumber, stored, treeThird z₁.laid z₂.laid⟩ R.second ρ.second a₃).map fun z₃ =>
    ⟨⟨(z₁.laid, z₂.laid, z₃.laid), (z₁.reads, z₂.reads, z₃.reads),
        (⟨(roundsOf z₁.laid).dropLast, z₁.cols⟩, ⟨roundsOf z₂.laid, z₂.cols⟩,
          ⟨roundsOf z₃.laid, z₃.cols⟩)⟩,
      (z₁.ver, z₂.ver, z₃.ver), (z₁.refused, z₂.refused, z₃.refused)⟩

/-- runC is ready and what follows it. -/
theorem runC_eq (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) (ρ : Draws) :
    runC F B H w₀ rc x c ρ =
      (ready F B H w₀ rc x c).bind (runFromReady F H (H.storedWords w₀ rc) x ρ) := rfl

/-- The second chain's first state, read through. -/
theorem meet_read (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    {R' : Ready W₀' Rc' Xi Ky Tr X₀ X} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (h : Ready.ReadThrough g rd R' R) (o₁ : Option (Mid (Local W₀' Rc' Xi Tr) X))
    (o₂ : Option (Mid (Common W₀' Rc' Ky) X₀)) :
    Option.map (Mid.narrow (Local.thru g rd))
        (o₁.bind fun m₁ => o₂.map fun m₂ => R'.start₃ (H.thru g rd d) m₁ m₂) =
      (o₁.map (Mid.narrow (Local.thru g rd))).bind fun m₁ =>
        (o₂.map (Mid.narrow (Common.thru g rd))).map fun m₂ => R.start₃ H m₁ m₂ := by
  cases o₁ with
  | none => rfl
  | some m₁ =>
    cases o₂ with
    | none => rfl
    | some m₂ => exact congrArg some (Ready.start₃_narrow g rd d H h m₁ m₂)

/-- **Behind ready, a run read through is the run.** -/
theorem runFromReady_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (stored : Nat → Nat → Option (List UInt64)) (x : Xi)
    (ρ : Draws) {R' : Ready W₀' Rc' Xi Ky Tr X₀ X} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (h : Ready.ReadThrough g rd R' R) :
    runFromReady F (H.thru g rd d) stored x ρ R' = runFromReady F H stored x ρ R := by
  unfold runFromReady
  refine bind_when_read (ChainProgress.narrow (Local.thru g rd))
    (ChainProgress.start_of_narrow (m' := some (R'.start₁ (H.thru g rd d))) _ _ _
      (congrArg some (Ready.start₁_narrow g rd d H h)) _ _)
    fun a₁ => ?_
  refine bind_when_read (ChainProgress.narrow (Local.thru g rd)) (walk_of_thru _ _ h.first _ _)
    fun z₁ => ?_
  by_cases hs : (!sealQuiet z₁.laid) = true
  · exact (if_pos hs).trans (if_pos hs).symm
  · refine (if_neg hs).trans (Eq.trans ?_ (if_neg hs).symm)
    refine bind_when_read (ChainProgress.narrow (Common.thru g rd))
      (ChainProgress.start_of_narrow (m' := some (R'.start₂ (H.thru g rd d))) _ _ _
        (congrArg some (Ready.start₂_narrow g rd d H h)) _ _)
      fun a₂ => ?_
    refine bind_when_read (ChainProgress.narrow (Common.thru g rd)) (walk_of_thru _ _ h.shared _ _)
      fun z₂ => ?_
    refine bind_when_read (ChainProgress.narrow (Local.thru g rd))
      (ChainProgress.start_of_narrow _ _ _ (meet_read g rd d H h z₁.mid z₂.mid) _ _) fun a₃ => ?_
    exact map_when_read (ChainProgress.narrow (Local.thru g rd)) (walk_of_thru _ _ h.second _ _)
      fun z₃ => rfl

/-- The columns of the prover read through are the prover's. -/
theorem storedWords_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀')
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') :
    (H.thru g rd d).storedWords w rc = H.storedWords (g w) (rd rc) := rfl

/-- **THE RUN OF THE PROVER READ THROUGH IS THE RUN OF THE PROVER**, at the index and the randomness
read through: the same refusal, or the same views, the same states of the verifier and the same
first rejections. -/
theorem runC_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (c : Coins B) (ρ : Draws)
    (hd : H.inRange (g d) = H.inRange H.dummy) :
    runC F B (H.thru g rd d) w rc x c ρ = runC F B H (g w) (rd rc) x c ρ := by
  rw [runC_eq, runC_eq, ready_thru g rd d F B H w rc x c hd]
  cases hR : ready F B H (g w) (rd rc) x c with
  | error e => rfl
  | ok R =>
    exact runFromReady_thru g rd d F H (H.storedWords (g w) (rd rc)) x ρ
      (Ready.reads_thru g rd hR)

/-! ## 6 The silent set and the outcome -/

/-- A part read through stops where the part stops. -/
theorem Part.stopAt_thru (see : V' → V) (wit : W' → W) (p : Part V W Y) (v : Option V)
    (v' : Option V') (hv : v'.map see = v) (loc ds : List Fmt.Drawn) :
    (p.thru see wit).stopAt v' loc ds = p.stopAt v loc ds := by
  have hl : (p.thru see wit).moves.length = p.moves.length := by
    show (p.moves.map _).length = p.moves.length
    rw [List.length_map]
  subst hv
  cases v' with
  | none =>
    show ((if (p.thru see wit).moves.length == 0 then [] else
        List.range ((p.thru see wit).moves.length + 1)).findSome? _) =
      ((if p.moves.length == 0 then [] else List.range (p.moves.length + 1)).findSome? _)
    rw [hl]
    try rfl
  | some u =>
    show ((if (p.thru see wit).moves.length == 0 then [] else
        List.range ((p.thru see wit).moves.length + 1)).findSome? _) =
      ((if p.moves.length == 0 then [] else List.range (p.moves.length + 1)).findSome? _)
    rw [hl]
    try rfl

/-- So does a list. -/
theorem rowStopAt_thru (see : V' → V) (wit : W' → W) (v : Option V) (v' : Option V')
    (hv : v'.map see = v) :
    (ps : List (Part V W Y)) → (loc ds : List Fmt.Drawn) →
      rowStopAt v' (ps.map (Part.thru see wit)) loc ds = rowStopAt v ps loc ds
  | [], _, _ => rfl
  | p :: ps, loc, ds => by
    have hl : (p.thru see wit).moves.length = p.moves.length := by
      show (p.moves.map _).length = p.moves.length
      rw [List.length_map]
    have h1 := Part.stopAt_thru see wit p v v' hv loc (ds.take p.moves.length)
    have h2 := rowStopAt_thru see wit v v' hv ps (loc ++ ds.take p.moves.length)
      (ds.drop p.moves.length)
    show ((p.thru see wit).stopAt v' loc (ds.take (p.thru see wit).moves.length)).or
        (rowStopAt v' (ps.map (Part.thru see wit)) (loc ++ ds.take (p.thru see wit).moves.length)
          (ds.drop (p.thru see wit).moves.length)) =
      (p.stopAt v loc (ds.take p.moves.length)).or
        (rowStopAt v ps (loc ++ ds.take p.moves.length) (ds.drop p.moves.length))
    rw [hl, h1, h2]

/-- And a chain. -/
theorem chainStopAt_thru (see : V' → V) (wit : W' → W) (v : Option V) (v' : Option V')
    (hv : v'.map see = v) (bs : List (Block S Cl)) (hs : List (Placed V W Y)) :
    ∀ loc ds : List Fmt.Drawn,
      chainStopAt v' bs (hs.map (Placed.thru see wit)) loc ds = chainStopAt v bs hs loc ds := by
  induction bs with
  | nil =>
    intro loc ds
    rfl
  | cons b bs ih =>
    intro loc ds
    have hfind : ((hs.map (Placed.thru see wit)).find? fun h => h.place == b.place) =
        (hs.find? fun h => h.place == b.place).map (Placed.thru see wit) := by
      rw [List.find?_map]
      rfl
    show (((hs.map (Placed.thru see wit)).find? fun h => h.place == b.place).bind fun h =>
          rowStopAt v' h.parts loc (ds.take b.rounds.length)).or
        (chainStopAt v' bs (hs.map (Placed.thru see wit)) (loc ++ ds.take b.rounds.length)
          (ds.drop b.rounds.length)) =
      ((hs.find? fun h => h.place == b.place).bind fun h =>
          rowStopAt v h.parts loc (ds.take b.rounds.length)).or
        (chainStopAt v bs hs (loc ++ ds.take b.rounds.length) (ds.drop b.rounds.length))
    rw [hfind, ih]
    cases hs.find? fun h => h.place == b.place with
    | none => rfl
    | some g =>
      show (rowStopAt v' (g.parts.map (Part.thru see wit)) loc (ds.take b.rounds.length)).or _ =
        (rowStopAt v g.parts loc (ds.take b.rounds.length)).or _
      rw [rowStopAt_thru see wit v v' hv g.parts]

/-- **The silent set of the prover read through is the prover's.** -/
theorem silentAt_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (ρ : Draws) :
    silentAt F (H.thru g rd d) w rc x ρ = silentAt F H (g w) (rd rc) x ρ := by
  have e : (H.thru g rd d).trace w x = H.trace (g w) x := rfl
  unfold silentAt
  rw [e]
  cases H.trace (g w) x with
  | none => rfl
  | some tr =>
    have h1 := chainStopAt_thru (Local.thru g rd) (Local.thru g rd)
      (Face.own.sees (⟨g w, rd rc, x, tr⟩ : Local W₀ Rc Xi Tr))
      (Face.own.sees (⟨w, rc, x, tr⟩ : Local W₀' Rc' Xi Tr)) rfl F.first.blocksInOrder H.first [] ρ.first
    have h2 := chainStopAt_thru id (Common.thru (Ky := Ky) g rd) none none rfl F.shared.blocksInOrder
      H.shared [] ρ.shared
    have h3 := chainStopAt_thru (Local.thru g rd) (Local.thru g rd)
      (Face.own.sees (⟨g w, rd rc, x, tr⟩ : Local W₀ Rc Xi Tr))
      (Face.own.sees (⟨w, rc, x, tr⟩ : Local W₀' Rc' Xi Tr)) rfl F.second.blocksInOrder H.second ρ.first
      ρ.second
    have key := congrArg₂ Option.or h1 (congrArg₂ Option.or h2 h3)
    exact key

/-- **The outcome of the prover read through is the prover's.** -/
theorem outcomeC_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (F : FileDescription Xi) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (c : Coins B) (ρ : Draws)
    (hd : H.inRange (g d) = H.inRange H.dummy) :
    outcomeC F B (H.thru g rd d) w rc x c ρ = outcomeC F B H (g w) (rd rc) x c ρ := by
  unfold outcomeC
  rw [silentAt_thru g rd d F H w rc x ρ, runC_thru g rd d F B H w rc x c ρ hd]

end ProofFile.Honest

#print axioms ProofFile.Honest.bind_when_read
#print axioms ProofFile.Honest.map_when_read
#print axioms ProofFile.Honest.unfit_map
#print axioms ProofFile.Honest.three_read
#print axioms ProofFile.Honest.pair_read
#print axioms ProofFile.Honest.append_read
#print axioms ProofFile.Honest.steps_read
#print axioms ProofFile.Honest.Step.thru
#print axioms ProofFile.Honest.zipSteps_thru
#print axioms ProofFile.Honest.Part.steps_thru
#print axioms ProofFile.Honest.RowCoins.thru
#print axioms ProofFile.Honest.lendPart_thru
#print axioms ProofFile.Honest.lendRow_thru
#print axioms ProofFile.Honest.rowSteps_thru
#print axioms ProofFile.Honest.Placed.steps_thru
#print axioms ProofFile.Honest.Placed.rounds_thru
#print axioms ProofFile.Honest.Placed.cuts_thru
#print axioms ProofFile.Honest.Placed.parts_thru
#print axioms ProofFile.Honest.idleSteps_thru
#print axioms ProofFile.Honest.chainSteps_thru
#print axioms ProofFile.Honest.strays_keep_places
#print axioms ProofFile.Honest.twice_keep_places
#print axioms ProofFile.Honest.twice_thru
#print axioms ProofFile.Honest.Prover.thru
#print axioms ProofFile.Honest.readyTests_thru
#print axioms ProofFile.Honest.readyWith
#print axioms ProofFile.Honest.readyAfter
#print axioms ProofFile.Honest.ready_eq
#print axioms ProofFile.Honest.Ready.thru
#print axioms ProofFile.Honest.sharedSteps_thru
#print axioms ProofFile.Honest.readyWith_thru
#print axioms ProofFile.Honest.readyAfter_thru
#print axioms ProofFile.Honest.ready_thru
#print axioms ProofFile.Honest.Ready.ReadThrough
#print axioms ProofFile.Honest.Ready.reads_thru
#print axioms ProofFile.Honest.Mid.narrow
#print axioms ProofFile.Honest.ChainProgress.narrow
#print axioms ProofFile.Honest.Step.tell_thru
#print axioms ProofFile.Honest.stops_read
#print axioms ProofFile.Honest.Step.hear_thru
#print axioms ProofFile.Honest.settleReads
#print axioms ProofFile.Honest.settleVer
#print axioms ProofFile.Honest.settleNext
#print axioms ProofFile.Honest.settleAt_wait
#print axioms ProofFile.Honest.settleAt_go
#print axioms ProofFile.Honest.took_read
#print axioms ProofFile.Honest.settleNext_narrow
#print axioms ProofFile.Honest.ChainProgress.settle_narrow
#print axioms ProofFile.Honest.ChainProgress.start_narrow
#print axioms ProofFile.Honest.ChainProgress.start_of_narrow
#print axioms ProofFile.Honest.ChainProgress.say_thru
#print axioms ProofFile.Honest.ChainProgress.heard_thru
#print axioms ProofFile.Honest.walk_thru
#print axioms ProofFile.Honest.walk_of_thru
#print axioms ProofFile.Honest.Ready.start₁_narrow
#print axioms ProofFile.Honest.Ready.start₂_narrow
#print axioms ProofFile.Honest.Ready.start₃_narrow
#print axioms ProofFile.Honest.runFromReady
#print axioms ProofFile.Honest.runC_eq
#print axioms ProofFile.Honest.meet_read
#print axioms ProofFile.Honest.runFromReady_thru
#print axioms ProofFile.Honest.storedWords_thru
#print axioms ProofFile.Honest.runC_thru
#print axioms ProofFile.Honest.Part.stopAt_thru
#print axioms ProofFile.Honest.rowStopAt_thru
#print axioms ProofFile.Honest.chainStopAt_thru
#print axioms ProofFile.Honest.silentAt_thru
#print axioms ProofFile.Honest.outcomeC_thru
