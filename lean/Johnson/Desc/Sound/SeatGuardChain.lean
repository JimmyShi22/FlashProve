-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeatGuardChain.lean: THE GUARD ON ONE SEAT (Johnson/Desc/SeatGuard.lean) AT THE WHOLE CHAIN: (1) the guarded chain's yes is the unguarded chain's yes, with the same end; (2) where
every part leaves the seat, the guarded chain's flat list IS the chain's: the theorem for the day when the guard is struck.

  Block.UnderR b' b: b' has b's rounds, and where b' says yes b says the same yes. step_under, fold_under, chainAt_under: then a step's, a fold's, a chain's yes goes over, with the same record, the same
    rounds and columns left.
  Link.BatchMono: THE ONE PREMISE ON A KIND's TEXT: the batching is monotone in the function of claims that it is handed: where f' says yes f says the same yes ⇒ L.batch f' has L.batch f's rounds and stands
    under it.
  underR_stamp: a driver's stamp of the place carries it. claimsInBy_under, afterIn_under: the guarded blocks' runs in a row say the runs' own yes.
  **Chain.guarded_chainAt**: every link's batching monotone ⇒ chainAt name ft (c.guarded same but).blocksInOrder s v = .ok e → chainAt name ft c.blocksInOrder s v = .ok e: THE GUARD CAN ONLY REFUSE MORE.
  Block.Still, Link.Still, Chain.Still: every part leaves the seat, in the guard's own word: at each yes, same t s = true (a block's decision: but at a place that but names). THE BATCHING IS ASKED AT THE LINK's OWN
    FUNCTION OF CLAIMS ALONE. (Asked at every function it is unpayable at a batching that goes on from its function's record, and the theorem empty there.)
  **Chain.Still.guarded_flat_eq**: c.Still same but → (c.guarded same but).blocksInOrder = c.blocksInOrder; Chain.guarded_last_rounds: and the last block's rounds are as they were. BY READING, NO THEOREM: Block.lean reads a description's chains by
    «.blocksInOrder» at every place but one, FileDescription.sealLast (:623: F.first.last.rounds): so the verdict is unchanged when the guard is struck.

Silly members. A batching that says yes just where its function refuses is not monotone: there the guarded chain can say yes where the chain says no: the premise is needed (SeatGuardChainToy's guard, which is not in this library, shows it).
same := fun _ _ => true: every chain is still, and the guard is idle. same := fun _ _ => false: a chain is still only if no part ever says yes.
Every "there is", walked: no statement has one.
Limits. Rules: shown of no chain of the protocol. Link.BatchMono is owed at the real batching's text (K9's files). Chain.Still is form (A)'s debt, kind by kind. Nothing on soundness, on acceptance or on hiding.

-/
import Johnson.Desc.Sound.SeatGuardLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-! ## 0 Two small facts on Except -/

theorem bindMono {ε α β : Type} {x : Except ε α} {f g : α → Except ε β} {y : β} (h : x.bind f = .ok y)
    (hfg : ∀ a, f a = .ok y → g a = .ok y) : x.bind g = .ok y := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact hfg a h

theorem bindMonoL {ε α β : Type} {x x' : Except ε α} {f : α → Except ε β} {y : β} (h : x.bind f = .ok y)
    (hx : ∀ a, x = .ok a → x' = .ok a) : x'.bind f = .ok y := by
  cases x with
  | error e => exact nomatch h
  | ok a => rw [hx a rfl]; exact h

/-! ## 1 A yes goes over -/

/-- b' has b's rounds, and where b' says yes b says the same yes. -/
def Block.UnderR (b' b : Block S Cl) : Prop := b'.rounds = b.rounds ∧ b'.Under b

/-- Two lists of blocks, member by member. (No Mathlib stands beneath this file: so the relation is typed here.) -/
inductive EachUnderR : List (Block S Cl) → List (Block S Cl) → Prop
  | nil : EachUnderR [] []
  | cons {b' b : Block S Cl} {l' l : List (Block S Cl)} : b'.UnderR b → EachUnderR l' l → EachUnderR (b' :: l') (b :: l)

theorem step_under {b' b : Block S Cl} (u : b'.UnderR b) {ft : Nat} {s : S} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} {x : S × Nat} (H : b'.step ft s rs cols = .ok x) : b.step ft s rs cols = .ok x := by
  unfold Block.step at H ⊢
  rw [u.1] at H
  refine bindMono H fun _ H => ?_
  refine bindMono H fun _ H => ?_
  exact bindMonoL H fun a ha => u.2 _ _ _ _ ha

theorem fold_under {ft : Nat} : ∀ {l' l : List (Block S Cl)}, EachUnderR l' l →
    ∀ {s : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn},
      foldBlocks ft l' s rs cols = .ok out → foldBlocks ft l s rs cols = .ok out
  | [], [], _, _, _, _, _, H => H
  | b' :: l', b :: l, .cons u ul, s, rs, cols, out, H => by
    simp only [foldBlocks, List.splitAt_eq] at H ⊢
    rw [u.1] at H
    split at H
    next => exact nomatch H
    next hlen =>
      rw [if_neg hlen]
      split at H
      next => exact nomatch H
      next s' k hst =>
        rw [step_under u hst]
        exact fold_under ul H

theorem chainAt_under {name : String} {ft : Nat} {l' l : List (Block S Cl)}
    (u : EachUnderR l' l) {s e : S} {v : Fmt.View}
    (H : chainAt name ft l' s v = .ok e) : chainAt name ft l s v = .ok e := by
  have F := fold_under u (chainAtOk H)
  have hne : l.isEmpty = false := by
    cases u with
    | nil => exact nomatch H
    | cons _ _ => rfl
  unfold chainAt
  rw [hne, F]
  rfl

/-! ## 2 The guarded chain's yes is the chain's -/

section
variable (same : S → S → Bool) (but : Place → Bool)

theorem guarded_underR (b : Block S Cl) : (b.guarded same but).UnderR b :=
  ⟨rfl, guarded_under same but b⟩

theorem guarded_map_underR : ∀ l : List (Block S Cl),
    EachUnderR (l.map (Block.guarded same but)) l
  | [] => .nil
  | b :: l => .cons (guarded_underR same but b) (guarded_map_underR l)

/-- A guarded block's run under a name is the guard on the block's run under that name. -/
theorem guarded_lookup_claims (b : Block S Cl) (n : String) :
    (b.guarded same but).claims.lookup n = (b.claims.lookup n).map fun r =>
      fun k t => (r k t).bind fun y => (seatSame same t y.2).map fun _ => y := by
  show (b.claims.map fun c =>
    (c.1, fun k t => (c.2 k t).bind fun y => (seatSame same t y.2).map fun _ => y)).lookup n = _
  induction b.claims with
  | nil => rfl
  | cons c l ih =>
    obtain ⟨k, r⟩ := c
    simp only [List.map_cons, List.lookup_cons]
    cases (n == k) with
    | true => rfl
    | false => exact ih

theorem guarded_lookup_after (b : Block S Cl) (n : String) :
    (b.guarded same but).after.lookup n = (b.after.lookup n).map fun r =>
      fun t => (r t).bind (seatSame same t) := by
  show (b.after.map fun c => (c.1, fun t => (c.2 t).bind (seatSame same t))).lookup n = _
  induction b.after with
  | nil => rfl
  | cons c l ih =>
    obtain ⟨k, r⟩ := c
    simp only [List.map_cons, List.lookup_cons]
    cases (n == k) with
    | true => rfl
    | false => exact ih

/-- One guarded run of claims says the run's own yes. -/
theorem claimsInStep_under (each : Nat × String → List Cl → S → Except String Unit)
    (bs : List (Block S Cl)) (x : List Cl × S) (o : Nat × String) (w : List Cl × S)
    (H : claimsInStep each (bs.map (Block.guarded same but)) x o = .ok w) :
    claimsInStep each bs x o = .ok w := by
  unfold claimsInStep at H ⊢
  rw [List.getElem?_map] at H
  cases hb : bs[o.1]? with
  | none => rw [hb] at H; exact nomatch H
  | some b =>
    rw [hb] at H
    have H1 : (named (o.2 ++ ": no such run") ((b.guarded same but).claims.lookup o.2)).bind _ = .ok w := H
    rw [guarded_lookup_claims] at H1
    show (named (o.2 ++ ": no such run") (b.claims.lookup o.2)).bind _ = .ok w
    cases hl : b.claims.lookup o.2 with
    | none => rw [hl] at H1; exact nomatch H1
    | some r =>
      rw [hl] at H1
      have H2 : (match (r x.1.length x.2).bind fun y => (seatSame same x.2 y.2).map fun _ => y with
        | .ok y =>
          match each o y.1 y.2 with
          | .ok _ => Except.ok (x.1 ++ y.1, y.2)
          | .error e => Except.error (o.2 ++ ": behind the run: " ++ e)
        | .error e => Except.error (o.2 ++ ": " ++ e)) = Except.ok w := H1
      show (match r x.1.length x.2 with
        | .ok y =>
          match each o y.1 y.2 with
          | .ok _ => Except.ok (x.1 ++ y.1, y.2)
          | .error e => Except.error (o.2 ++ ": behind the run: " ++ e)
        | .error e => Except.error (o.2 ++ ": " ++ e)) = Except.ok w
      cases hr : r x.1.length x.2 with
      | error e => rw [hr] at H2; exact nomatch H2
      | ok y =>
        rw [hr] at H2
        cases hg : seatSame same x.2 y.2 with
        | error e =>
          have H3 : (match (seatSame same x.2 y.2).map fun _ => y with
            | .ok y =>
              match each o y.1 y.2 with
              | .ok _ => Except.ok (x.1 ++ y.1, y.2)
              | .error e => Except.error (o.2 ++ ": behind the run: " ++ e)
            | .error e => Except.error (o.2 ++ ": " ++ e)) = Except.ok w := H2
          rw [hg] at H3; exact nomatch H3
        | ok u =>
          have H3 : (match (seatSame same x.2 y.2).map fun _ => y with
            | .ok y =>
              match each o y.1 y.2 with
              | .ok _ => Except.ok (x.1 ++ y.1, y.2)
              | .error e => Except.error (o.2 ++ ": behind the run: " ++ e)
            | .error e => Except.error (o.2 ++ ": " ++ e)) = Except.ok w := H2
          rw [hg] at H3
          exact H3

/-- A fold of such steps from a refusal is that refusal. -/
theorem foldlErr {ε σ ι : Type} (f : σ → ι → Except ε σ) (e : ε) : ∀ l : List ι,
    l.foldl (fun (acc : Except ε σ) o => acc.bind fun x => f x o) (Except.error e) = Except.error e
  | [] => rfl
  | _ :: l => foldlErr f e l

/-- A fold of steps over Except: a yes goes over, step by step. -/
theorem foldlMono {ε σ ι : Type} (f' f : σ → ι → Except ε σ) (h : ∀ x o w, f' x o = .ok w → f x o = .ok w) :
    ∀ (l : List ι) (acc : Except ε σ) (w : σ),
      l.foldl (fun (acc : Except ε σ) o => acc.bind fun x => f' x o) acc = .ok w →
      l.foldl (fun (acc : Except ε σ) o => acc.bind fun x => f x o) acc = .ok w
  | [], _, _, H => H
  | o :: l, .error e, w, H => by
    have H' : l.foldl (fun (acc : Except ε σ) o => acc.bind fun x => f' x o) (Except.error e) = .ok w := H
    rw [foldlErr] at H'
    exact nomatch H'
  | o :: l, .ok x, w, H => by
    have H' : l.foldl (fun (acc : Except ε σ) o => acc.bind fun x => f' x o) (f' x o) = .ok w := H
    show l.foldl (fun (acc : Except ε σ) o => acc.bind fun x => f x o) (f x o) = .ok w
    cases hx : f' x o with
    | error e =>
      rw [hx, foldlErr] at H'
      exact nomatch H'
    | ok z =>
      rw [hx] at H'
      rw [h x o z hx]
      exact foldlMono f' f h l (.ok z) w H'

theorem claimsInBy_under (each : Nat × String → List Cl → S → Except String Unit) (bs : List (Block S Cl))
    (order : List (Nat × String)) (s : S) (y : List Cl × S)
    (H : claimsInBy each (bs.map (Block.guarded same but)) order s = .ok y) :
    claimsInBy each bs order s = .ok y :=
  foldlMono _ _ (claimsInStep_under same but each bs) order _ y H

/-- One guarded run behind the batching says the run's own yes. -/
theorem afterStep_under (bs : List (Block S Cl)) (x : S) (o : Nat × String) (w : S)
    (H : ((named (o.2 ++ ": no such run")
        (((bs.map (Block.guarded same but))[o.1]?).bind fun b => b.after.lookup o.2)).bind fun run =>
      match run x with
      | .ok y => Except.ok y
      | .error e => Except.error (o.2 ++ ": " ++ e)) = .ok w) :
    ((named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.after.lookup o.2)).bind fun run =>
      match run x with
      | .ok y => Except.ok y
      | .error e => Except.error (o.2 ++ ": " ++ e)) = .ok w := by
  rw [List.getElem?_map] at H
  cases hb : bs[o.1]? with
  | none => rw [hb] at H; exact nomatch H
  | some b =>
    rw [hb] at H
    have H1 : (named (o.2 ++ ": no such run") ((b.guarded same but).after.lookup o.2)).bind _ = .ok w := H
    rw [guarded_lookup_after] at H1
    show (named (o.2 ++ ": no such run") (b.after.lookup o.2)).bind _ = .ok w
    cases hl : b.after.lookup o.2 with
    | none => rw [hl] at H1; exact nomatch H1
    | some r =>
      rw [hl] at H1
      have H2 : (match (r x).bind (seatSame same x) with
        | .ok y => Except.ok y
        | .error e => Except.error (o.2 ++ ": " ++ e)) = Except.ok w := H1
      show (match r x with
        | .ok y => Except.ok y
        | .error e => Except.error (o.2 ++ ": " ++ e)) = Except.ok w
      cases hr : r x with
      | error e => rw [hr] at H2; exact nomatch H2
      | ok y =>
        rw [hr] at H2
        have H3 : (match seatSame same x y with
          | .ok y => Except.ok y
          | .error e => Except.error (o.2 ++ ": " ++ e)) = Except.ok w := H2
        cases hg : seatSame same x y with
        | error e => rw [hg] at H3; exact nomatch H3
        | ok u =>
          rw [hg] at H3
          rw [← (seatSame_ok hg).1]
          exact H3

theorem afterIn_under (bs : List (Block S Cl)) (order : List (Nat × String)) (s s' : S)
    (H : afterIn (bs.map (Block.guarded same but)) order s = .ok s') : afterIn bs order s = .ok s' :=
  foldlMono _ _ (afterStep_under same but bs) order _ s' H

/-- **The one premise on a kind's text**: the batching is monotone in the function of claims that it is handed. -/
def Link.BatchMono (L : Link S Cl) : Prop :=
  ∀ f' f : S → Except String (List Cl × S), (∀ s y, f' s = .ok y → f s = .ok y) →
    (L.batch f').UnderR (L.batch f)

/-- A stamp of the place turns neither rounds nor decision: so a batching that a driver stamps is monotone where the maker that it was handed is. -/
theorem underR_stamp {b' b : Block S Cl} (u : b'.UnderR b) (a : Place) :
    Block.UnderR { b' with place := a } { b with place := a } := ⟨u.1, fun s rs gs s' D => u.2 s rs gs s' D⟩

theorem Block.UnderR.trans {a b c : Block S Cl} (h₁ : a.UnderR b) (h₂ : b.UnderR c) : a.UnderR c :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem forall₂_append {l₁' l₁ l₂' l₂ : List (Block S Cl)} (h₁ : EachUnderR l₁' l₁)
    (h₂ : EachUnderR l₂' l₂) : EachUnderR (l₁' ++ l₂') (l₁ ++ l₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons u _ ih => exact .cons u ih

theorem Link.guarded_flat_under (L : Link S Cl) (hb : L.BatchMono) :
    EachUnderR (L.guarded same but).blocksInOrder L.blocksInOrder := by
  unfold Link.blocksInOrder
  refine forall₂_append (forall₂_append (forall₂_append (l₁' := _ :: _) (l₁ := _ :: _)
    (.cons ⟨rfl, fun t _ _ s' D => ?_⟩ (guarded_map_underR same but L.hear))
    (.cons ?_ (.cons ⟨rfl, fun t _ _ s' D => ?_⟩ .nil))) (guarded_map_underR same but L.close))
    (.cons ⟨rfl, fun t _ _ s' D => ?_⟩ .nil)
  · obtain ⟨s, hs, e⟩ := bindOk (x := L.lay t) D
    rw [(seatSame_ok e).1]
    exact hs
  · exact (guarded_underR same but _).trans
      (hb _ _ fun s y K => claimsInBy_under same but L.each L.hear L.order s y K)
  · have D' : (L.guarded same but).runBehind t = .ok s' := D
    show L.runBehind t = .ok s'
    unfold Link.runBehind at D' ⊢
    have D'' : (match L.tests t with
      | .ok _ => afterIn (L.hear.map (Block.guarded same but)) L.orderAfter t
      | .error e => .error ("the tests behind the adding: " ++ e)) = .ok s' := D'
    cases ht : L.tests t with
    | error e => rw [ht] at D''; exact nomatch D''
    | ok u =>
      rw [ht] at D''
      exact afterIn_under same but L.hear L.orderAfter t s' D''
  · obtain ⟨s, hs, e⟩ := bindOk (x := L.clear t) D
    rw [(seatSame_ok e).1]
    exact hs

theorem bare_underR {b' b : Block S Cl} (u : b'.UnderR b) :
    Block.UnderR { b' with planOk := b'.planOk && b'.hasNoClaimsAndNothingAfter } { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } :=
  ⟨u.1, fun s rs gs s' D => u.2 s rs gs s' D⟩

theorem Chain.guarded_flat_under (c : Chain S Cl) (hb : ∀ L ∈ c.links, L.BatchMono) :
    EachUnderR (c.guarded same but).blocksInOrder c.blocksInOrder := by
  have hm : ∀ l : List (Block S Cl), EachUnderR
      ((l.map (Block.guarded same but)).map fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter })
      (l.map fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) := by
    intro l
    induction l with
    | nil => exact .nil
    | cons b l ih => exact .cons (bare_underR (guarded_underR same but b)) ih
  have hl : ∀ ls : List (Link S Cl), (∀ L ∈ ls, L.BatchMono) → EachUnderR
      ((ls.map (Link.guarded same but)).flatMap Link.blocksInOrder) (ls.flatMap Link.blocksInOrder) := by
    intro ls
    induction ls with
    | nil => intro _; exact .nil
    | cons L ls ih =>
      intro h
      exact forall₂_append (Link.guarded_flat_under same but L (h L (List.mem_cons_self ..)))
        (ih fun L' m => h L' (List.mem_cons_of_mem _ m))
  unfold Chain.blocksInOrder
  exact forall₂_append (forall₂_append (forall₂_append (l₁' := _ :: _) (l₁ := _ :: _)
    (.cons (bare_underR (guarded_underR same but c.first)) (hm c.front)) (hl c.links hb)) (hm c.back))
    (.cons (bare_underR (guarded_underR same but c.last)) .nil)

/-- **THE GUARD CAN ONLY REFUSE MORE: the guarded chain's yes is the chain's yes, with the same end.** -/
theorem Chain.guarded_chainAt (c : Chain S Cl) (hb : ∀ L ∈ c.links, L.BatchMono) {name : String} {ft : Nat}
    {s e : S} {v : Fmt.View} (H : chainAt name ft (c.guarded same but).blocksInOrder s v = .ok e) :
    chainAt name ft c.blocksInOrder s v = .ok e :=
  chainAt_under (Chain.guarded_flat_under same but c hb) H

/-! ## 3 The day when the guard is struck -/

/-- The block never writes the seat, in the guard's own word: its decision (but at a place that but names), each run of claims, each run behind the batching. -/
def Block.Still (b : Block S Cl) : Prop :=
  (but b.place = false → ∀ t rs gs s, b.decide t rs gs = .ok s → same t s = true) ∧
  (∀ c ∈ b.claims, ∀ n t y, c.2 n t = .ok y → same t y.2 = true) ∧
  (∀ c ∈ b.after, ∀ t s, c.2 t = .ok s → same t s = true)

/-- The like for a link's five parts that can write. -/
structure Link.Still (L : Link S Cl) : Prop where
  lay : ∀ t s, L.lay t = .ok s → same t s = true
  hear : ∀ b ∈ L.hear, b.Still same but
  /-- AT THE LINK's OWN FUNCTION OF CLAIMS ALONE: a batching that goes on from its function's record cannot be still at a function that writes the seat -/
  batch : (L.batch (claimsInBy L.each L.hear L.order)).Still same but
  close : ∀ b ∈ L.close, b.Still same but
  clear : ∀ t s, L.clear t = .ok s → same t s = true

/-- The like for a chain. -/
structure Chain.Still (c : Chain S Cl) : Prop where
  first : c.first.Still same but
  front : ∀ b ∈ c.front, b.Still same but
  links : ∀ L ∈ c.links, L.Still same but
  back : ∀ b ∈ c.back, b.Still same but
  last : c.last.Still same but

variable {same but}

theorem bindSame {t : S} {x : Except String S} (h : ∀ s, x = .ok s → same t s = true) :
    x.bind (seatSame same t) = x := by
  cases x with
  | error e => rfl
  | ok s =>
    show seatSame same t s = .ok s
    unfold seatSame
    rw [h s rfl]; rfl

theorem mapSelf {β : Type} {f : β → β} : ∀ {l : List β}, (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | x :: l, h => by
    rw [List.map_cons, h x (List.mem_cons_self ..), mapSelf fun y m => h y (List.mem_cons_of_mem _ m)]

/-- A block that never writes the seat IS its guarded form. -/
theorem Block.Still.guarded_eq {b : Block S Cl} (h : b.Still same but) : b.guarded same but = b := by
  have hd : (fun t rs gs => if but b.place then b.decide t rs gs
      else (b.decide t rs gs).bind (seatSame same t)) = b.decide := by
    funext t rs gs
    split
    · rfl
    · rename_i hn
      exact bindSame fun s e => h.1 (Bool.eq_false_iff.2 hn) t rs gs s e
  have hc : (b.claims.map fun c =>
      (c.1, fun n t => (c.2 n t).bind fun y => (seatSame same t y.2).map fun _ => y)) = b.claims := by
    refine mapSelf fun c m => Prod.ext rfl (funext fun n => funext fun t => ?_)
    show ((c.2 n t).bind fun y => (seatSame same t y.2).map fun _ => y) = c.2 n t
    cases hy : c.2 n t with
    | error e => rfl
    | ok y =>
      show (seatSame same t y.2).map (fun _ => y) = .ok y
      unfold seatSame
      rw [h.2.1 c m n t y hy]; rfl
  have ha : (b.after.map fun c => (c.1, fun t => (c.2 t).bind (seatSame same t))) = b.after :=
    mapSelf fun c m => Prod.ext rfl (funext fun t => bindSame fun s e => h.2.2 c m t s e)
  unfold Block.guarded
  rw [hd, hc, ha]

/-- **A still link's guarded flat list IS its flat list.** (Not: the guarded link is the link: their two fields batch part at a function of claims that writes the seat.) -/
theorem Link.Still.guarded_flat_eq {L : Link S Cl} (h : L.Still same but) : (L.guarded same but).blocksInOrder = L.blocksInOrder := by
  have h1 : (fun t => (L.lay t).bind (seatSame same t)) = L.lay :=
    funext fun t => bindSame fun s e => h.lay t s e
  have h2 : L.hear.map (Block.guarded same but) = L.hear := mapSelf fun b m => (h.hear b m).guarded_eq
  have h3 : (L.batch (claimsInBy L.each L.hear L.order)).guarded same but =
      L.batch (claimsInBy L.each L.hear L.order) := h.batch.guarded_eq
  have h4 : L.close.map (Block.guarded same but) = L.close := mapSelf fun b m => (h.close b m).guarded_eq
  have h5 : (fun t => (L.clear t).bind (seatSame same t)) = L.clear :=
    funext fun t => bindSame fun s e => h.clear t s e
  have e : L.guarded same but = { L with batch := fun f => (L.batch f).guarded same but } := by
    unfold Link.guarded
    rw [h1, h2, h4, h5]
  have hR : Link.runBehind { L with batch := fun f => (L.batch f).guarded same but } = L.runBehind := rfl
  rw [e]
  unfold Link.blocksInOrder
  rw [hR]
  dsimp only
  rw [h3]

theorem flatMapSelf {ls : List (Link S Cl)} (h : ∀ L ∈ ls, L.Still same but) :
    (ls.map (Link.guarded same but)).flatMap Link.blocksInOrder = ls.flatMap Link.blocksInOrder := by
  induction ls with
  | nil => rfl
  | cons L ls ih =>
    simp only [List.map_cons, List.flatMap_cons]
    rw [(h L (List.mem_cons_self ..)).guarded_flat_eq, ih fun L' m => h L' (List.mem_cons_of_mem _ m)]

/-- **WHERE EVERY PART LEAVES THE SEAT, THE GUARDED CHAIN's FLAT LIST IS THE CHAIN's.** -/
theorem Chain.Still.guarded_flat_eq {c : Chain S Cl} (h : c.Still same but) : (c.guarded same but).blocksInOrder = c.blocksInOrder := by
  unfold Chain.blocksInOrder Chain.guarded
  dsimp only
  rw [h.first.guarded_eq, mapSelf fun b m => (h.front b m).guarded_eq, flatMapSelf h.links,
    mapSelf fun b m => (h.back b m).guarded_eq, h.last.guarded_eq]

/-- The one thing that Block.lean reads of a chain past its flat list (FileDescription.sealLast): the guard does not turn it. No premise. -/
theorem Chain.guarded_last_rounds (c : Chain S Cl) : (c.guarded same but).last.rounds = c.last.rounds := rfl

end

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.underR_stamp
#print axioms VerifiableInference.Desc.Chain.guarded_last_rounds
#print axioms VerifiableInference.Desc.step_under
#print axioms VerifiableInference.Desc.fold_under
#print axioms VerifiableInference.Desc.chainAt_under
#print axioms VerifiableInference.Desc.claimsInBy_under
#print axioms VerifiableInference.Desc.afterIn_under
#print axioms VerifiableInference.Desc.Link.guarded_flat_under
#print axioms VerifiableInference.Desc.Chain.guarded_flat_under
#print axioms VerifiableInference.Desc.Chain.guarded_chainAt
#print axioms VerifiableInference.Desc.Block.Still.guarded_eq
#print axioms VerifiableInference.Desc.Link.Still.guarded_flat_eq
#print axioms VerifiableInference.Desc.Chain.Still.guarded_flat_eq
