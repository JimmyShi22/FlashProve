-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Req/Names.lean: the names, and so the numbers, of the rounds that each routine of the
frame of a proof's first chain adds.

Main names:
  `namesOf F`: the names of a list of rounds.
  `Says x N`: wherever x ends well it has added rounds with just the names N, in this order.
  `Says.bind`, `Says.after`, `Says.before`, `Says.ite`, `says_reads`: the rules.
  `laidIdle_says`: what a routine that says N has laid has the names N.
  `says_reqSend`: SEND seed, and SEND answer where the sending has a round of its own for the
    answers. `says_loc`: LOC. `says_bat`: BAT. `says_fold`: FOLD epsilon, then k times FOLD round,
    for the k of the group. `says_cs`: SEND seed, CS. `says_base`: BASE lambda, BASE. `stageNames`,
    `says_stages`, `says_iopp`: BAT, then fold and code switch stage by stage, then the last step.
    `says_psc`, `says_batt`: BAT-sigma, PSC epsilon, kCol times PSC round. `says_linFirst`: SEND
    seed, SEND answer. `says_seal`: SEAL.
  `says_reply`, `says_sendOf`, `says_switch`, `says_battOf`: the parts of
    OnBytes/Tie/Pv/Req/Frame.lean.

Limits: names and numbers of rounds alone: no other field of a round is said. Nothing is said on
hiding.
-/
import OnBytes.Tie.Pv.Req.Kinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Req

open OnBytes OnBytes.Params
open OnBytes.Tie.Pv.Tail (Idle Reads plan_bind close_shuts none_shuts)

/-- The names of a list of rounds. -/
def namesOf (F : List PlanRound) : List String := F.map (·.entry.name)

/-- Wherever x ends well it has added rounds with just the names N, in this order. -/
def Says {α : Type} (x : Planning α) (N : List String) : Prop :=
  ∀ p a q, x p = .ok (a, q) → ∃ F, Adds p q F ∧ namesOf F = N

section Calculus
variable {α β : Type}

theorem says_reads {x : Planning α} (h : Reads x) : Says x [] := fun p a q hq => by
  obtain rfl := h p a q hq
  exact ⟨[], Adds.refl _, rfl⟩

theorem Says.bind {x : Planning α} {f : α → Planning β} {N N' : List String} (hx : Says x N)
    (hf : ∀ a, Says (f a) N') : Says (x >>= f) (N ++ N') := fun p b q h => by
  obtain ⟨a, m, h1, h2⟩ := plan_bind h
  obtain ⟨F, e1, n1⟩ := hx p a m h1
  obtain ⟨G, e2, n2⟩ := hf a m b q h2
  exact ⟨F ++ G, e1.trans e2, by simp [namesOf] at *; rw [n1, n2]⟩

/-- A step that says nothing, in front. -/
theorem Says.after {x : Planning α} {f : α → Planning β} {N : List String} (hx : Says x [])
    (hf : ∀ a, Says (f a) N) : Says (x >>= f) N := Says.bind hx hf

/-- A step that says nothing, behind. -/
theorem Says.before {x : Planning α} {f : α → Planning β} {N : List String} (hx : Says x N)
    (hf : ∀ a, Says (f a) []) : Says (x >>= f) N := by
  have h := Says.bind hx hf
  rwa [List.append_nil] at h

theorem says_pure (a : α) : Says (pure a : Planning α) [] := says_reads (Reads.pure a)

theorem Says.ite {c : Prop} [Decidable c] {x y : Planning α} {N N' : List String}
    (hx : Says x N) (hy : Says y N') : Says (if c then x else y) (if c then N else N') := by
  split
  · exact hx
  · exact hy

/-- What a routine that says N has laid has the names N. -/
theorem laidIdle_says {st : Setting} {x : Planning α} {N : List String} {F : List PlanRound}
    (h : Says x N) (k : LaidIdle st x F) : namesOf F = N := by
  obtain ⟨p, a, q, _, hq, e⟩ := k
  obtain ⟨G, e', n⟩ := h p a q hq
  rw [adds_inj e e']
  exact n

end Calculus

/-! ### The planner's own steps -/

theorem says_close (name : String) (why : ErrorKind) (e : Bound) (d : Draws) :
    Says (close name why e d) [name] := fun p _ q h => by
  obtain ⟨_, _, _, _, _, R, r, n⟩ := close_shuts h
  exact ⟨[R], Adds.push r, by simp [namesOf, n]⟩

theorem says_none (name : String) : Says (closeNone name) [name] := fun p _ q h => by
  obtain ⟨_, _, _, _, _, R, r, n⟩ := none_shuts h
  exact ⟨[R], Adds.push r, by simp [namesOf, n]⟩

theorem says_scalars (n : Nat) : Says (planScalars n) [] := fun p _ q h => by
  obtain rfl : { p with openBytes := p.openBytes + 24 * n } = q :=
    (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨[], Adds.refl _, rfl⟩

theorem says_answers (n : Nat) : Says (planAnswers n) [] := fun p _ q h => by
  obtain rfl : { p with openBytes := p.openBytes + 24 * n,
                        openAnswers := p.openAnswers + n } = q :=
    (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨[], Adds.refl _, rfl⟩

theorem says_roots (n : Nat) : Says (planRoots n) [] := fun p _ q h => by
  obtain rfl : { p with openBytes := p.openBytes + 32 * n,
                        openRoots := p.openRoots + n } = q :=
    (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨[], Adds.refl _, rfl⟩

/-! ### The frame's routines -/

theorem says_send (o : List SampleSize) (roots : Nat) (b : Bool) :
    Says (planSend o roots b)
      ("SEND seed" :: (if b = true then ["SEND answer"] else [])) :=
  Says.after (says_reads Tail.reads_setting) fun s =>
    Says.after (says_roots roots) fun _ =>
      Says.after (says_reads (Tail.reads_errors s o _)) fun _ =>
        Says.bind (N := ["SEND seed"]) (says_close _ _ _ _) fun _ =>
          Says.after (says_answers _) fun _ => Says.ite (says_none _) (says_pure _)

theorem says_reqSend (codes : Codes) (sent : List OracleNotice) (group atStart : GroupSize)
    (riders : Nat) (b : Bool) :
    Says (reqSend codes sent group atStart riders b)
      ("SEND seed" :: (if b = true then ["SEND answer"] else [])) :=
  Says.after (says_reads (reads_must _ _)) fun _ => says_send _ _ _

theorem says_bat (groups : List GroupSize) (rows : Nat) : Says (planBat groups rows) ["BAT"] :=
  Says.after (says_reads Tail.reads_setting) fun _ =>
    Says.after (says_reads (Tail.reads_list groups)) fun _ => says_close _ _ _ _

theorem says_batSigma (rows : Nat) : Says (planBatSigma rows) ["BAT-sigma"] :=
  Says.after (says_reads Tail.reads_setting) fun _ => says_close _ _ _ _

theorem says_loc (g : GroupSize) : Says (planLoc g) ["LOC"] :=
  Says.after (says_reads (Tail.reads_analysis g)) fun _ =>
    Says.after (says_reads (reads_positions _ _)) fun _ =>
      Says.after (says_reads (Tail.reads_needs _ _)) fun _ =>
        Says.before (says_close _ _ _ _) fun _ =>
          Says.after (says_reads (reads_listed _ _)) fun _ => says_pure _

theorem says_foldFrom (s : Setting) (g : GroupSize) (a : Analysis) :
    ∀ fuel j, Says (planFoldFrom s g a fuel j) (List.replicate fuel "FOLD round")
  | 0, _ => says_pure ()
  | fuel + 1, j =>
    Says.after (says_scalars 2) fun _ =>
      Says.bind (N := ["FOLD round"]) (says_close _ _ _ _) fun _ => says_foldFrom s g a fuel (j + 1)

theorem says_fold (g : GroupSize) (roots : Nat) :
    Says (planFold g roots) ("FOLD epsilon" :: List.replicate g.k "FOLD round") :=
  Says.after (says_reads Tail.reads_setting) fun _ =>
    Says.after (says_reads (Tail.reads_analysis g)) fun _ =>
      Says.after (says_roots roots) fun _ =>
        Says.after (says_scalars 1) fun _ =>
          Says.bind (N := ["FOLD epsilon"]) (says_close _ _ _ _) fun _ =>
            Says.after (says_reads (Tail.reads_analysis g)) fun _ =>
              Says.after (says_reads Tail.reads_setting) fun _ => says_foldFrom _ g _ _ _

theorem says_cs (source target : GroupSize) (cubeBits oldRows symbols roots : Nat) :
    Says (planCs source target cubeBits oldRows symbols roots) ["SEND seed", "CS"] :=
  Says.after (says_reads Tail.reads_setting) fun _ =>
    Says.after (says_reads (Tail.reads_analysis source)) fun _ =>
      Says.after (says_reads (Tail.reads_analysis target)) fun _ =>
        Says.bind (N := ["SEND seed"]) (says_send _ _ false) fun _ =>
          Says.after (says_reads reads_scope) fun _ =>
            Says.after (says_reads (Tail.reads_needs _ _)) fun _ =>
              Says.before (says_close _ _ _ _) fun _ =>
                Says.after (says_reads (reads_listed _ _)) fun _ => says_pure _

theorem says_base (g : GroupSize) (roots : Nat) :
    Says (planBase g roots) ["BASE lambda", "BASE"] :=
  Says.after (says_reads Tail.reads_setting) fun _ =>
    Says.after (says_reads (Tail.reads_analysis g)) fun _ =>
      Says.after (says_roots roots) fun _ =>
        Says.after (says_scalars 1) fun _ =>
          Says.bind (N := ["BASE lambda"]) (says_close _ _ _ _) fun _ =>
            Says.after (says_scalars _) fun _ =>
              Says.after (says_reads (reads_positions _ _)) fun _ =>
                Says.after (says_reads (Tail.reads_needs _ _)) fun _ =>
                  Says.before (says_close _ _ _ _) fun _ =>
                    Says.after (says_reads (reads_listed _ _)) fun _ => says_pure _

/-- The names of the rounds of the stages of a proximity test. -/
def stageNames : List StageSize → List String
  | x :: y :: rest =>
    ("FOLD epsilon" :: List.replicate x.g.k "FOLD round") ++ (["SEND seed", "CS"] ++
      stageNames (y :: rest))
  | [_] => ["BASE lambda", "BASE"]
  | [] => []

theorem says_stages (fm : Nat) (ride : Bool) :
    ∀ (l : List StageSize) (first : Bool), Says (planStages fm ride first l) (stageNames l)
  | [], _ => fun _ _ _ h => by cases h
  | [x], _ => Says.before (says_base x.g _) fun _ => says_reads (Tail.reads_needs _ _)
  | x :: y :: rest, _ =>
    Says.bind (says_fold x.g _) fun _ =>
      Says.bind (says_cs _ _ _ _ _ _) fun _ =>
        Says.after (says_reads (Tail.reads_needs _ _)) fun _ =>
          says_stages fm ride (y :: rest) false

theorem says_iopp (l : List StageSize) (rows fm : Nat) (ride : Bool) :
    Says (planIopp l rows fm ride) ("BAT" :: stageNames l) :=
  Says.after (says_reads (Tail.reads_needs _ _)) fun _ =>
    Says.bind (N := ["BAT"]) (says_bat _ _) fun _ => says_stages fm ride l true

theorem says_seal : Says planSeal ["SEAL"] := says_close _ _ _ _

theorem says_linFirst (codes : Codes) (x : LinSized) :
    Says (linPlanFirst codes x) ["SEND seed", "SEND answer"] :=
  Says.after (says_reads (reads_must _ _)) fun _ => says_send _ _ true

theorem says_pscRounds (s' : Setting) :
    ∀ g : List Nat, Says (planPscRounds s' g) (List.replicate g.length "PSC round")
  | [] => says_pure ()
  | _ :: g =>
    Says.after (says_scalars _) fun _ =>
      Says.bind (N := ["PSC round"]) (says_close _ _ _ _) fun _ => says_pscRounds s' g

theorem says_psc (z : PscSize) :
    Says (planPsc z) ("PSC epsilon" :: (List.replicate z.degree.length "PSC round" ++
      (if z.withY = true then ["PSC Y", "PSC values"] else []))) :=
  Says.after (says_reads Tail.reads_setting) fun s' =>
    Says.after (says_scalars 1) fun _ =>
      Says.bind (N := ["PSC epsilon"]) (says_close _ _ _ _) fun _ =>
        Says.bind (says_pscRounds s' z.degree) fun _ =>
          Says.ite
            (Says.after (says_scalars _) fun _ =>
              Says.bind (N := ["PSC Y"]) (says_close _ _ _ _) fun _ =>
                Says.after (says_scalars _) fun _ => says_none _)
            (says_pure ())

theorem says_batt (rows kCol : Nat) :
    Says (planBatt rows kCol)
      ("BAT-sigma" :: "PSC epsilon" :: List.replicate kCol "PSC round") := by
  have h := Says.bind (says_batSigma rows) fun _ =>
    says_psc { degree := List.replicate kCol 3, withY := false }
  simpa using h

/-! ### The stretches of the frame, by name -/

section Stretches
variable {st : Setting} {z : ProofSized} {sub : Subproofs}

theorem says_reply (links : List ReqLink) :
    Says (replyOf links)
      (if ((links.head?.map (·.plain)).getD 0 != 0) = true then ["REPLY"] else []) :=
  Says.ite (Says.after (says_scalars _) fun _ => says_none _) (says_pure ())

theorem says_sendOf (l : Nat) (g : ReqGroup) (links : List ReqLink) :
    Says (sendOf z l g links)
      ("SEND seed" :: (if (l == 0) = true then ["SEND answer"] else [])) :=
  says_reqSend _ _ _ _ _ _

theorem says_switch (l : Nat) (g : ReqGroup) (links : List ReqLink) (before : GroupSize) :
    Says (switchOf z l g links before)
      (("SEND seed" :: (if (l == 0) = true then ["SEND answer"] else [])) ++
        (if 0 < l then ["LOC"] else [])) :=
  Says.bind (says_sendOf l g links) fun _ =>
    Says.ite (Says.before (says_loc before) fun _ => says_pure _) (says_pure _)

theorem says_battOf :
    Says (battOf z sub) (if 1 < sub.pendingRows then
      "BAT-sigma" :: "PSC epsilon" :: List.replicate z.batch.shape.kCol "PSC round" else []) :=
  Says.ite (says_batt _ _) (says_pure ())

end Stretches

end OnBytes.Tie.Pv.Req

#print axioms OnBytes.Tie.Pv.Req.says_iopp
#print axioms OnBytes.Tie.Pv.Req.says_fold
#print axioms OnBytes.Tie.Pv.Req.says_sendOf
#print axioms OnBytes.Tie.Pv.Req.says_switch
#print axioms OnBytes.Tie.Pv.Req.says_battOf
#print axioms OnBytes.Tie.Pv.Req.laidIdle_says
