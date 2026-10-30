-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/PlanSeats.lean: NO PART OF THE DESCRIPTION: THE SEATS OF THE FIRST CHAIN's ORACLE MESSAGES,
OFF THE PLAN, WITH CODE: for every sending of the proof file's first chain (the planner's own list: Johnson/G/Sends.lean:
frameSends), every oracle message with: its segment (link) and moment; its tree through the file and its place there (by
OnBytes.layTrees, OnBytes/Iop/Ground.lean; the entries' roots in front of the sending's entry); whether it is sampled; ITS ROLE: the carried message
of the switch into the group · a KEPT COPY, with as what it was first sent (ReqGroup.born: link, number in that link's list)
· one of the link's OWN messages, with its number in the link's list · the fold's fresh mask · a message of the very first
prover's message that belongs to no link's group (ReqShape.atStart) · a message of the last test's switches · W's sending.
THE ROLES ARE LAID BY THE ORDER IN WHICH frameSends LISTS A SENDING's MEMBERS (read at its text): the carried one (from the
second group on), the kept copies, the own messages of moment 0, the fresh mask, and at link 0 the messages atStart. A test
(rolesFit) holds each role's shape against the notice that the planner's list has at that place.
It reads nothing and writes nothing: the caller hands it values.
-/
import Johnson.Desc.ProofFile.Pub

open VerifiableInference.Desc

namespace P5T

inductive Role where
  | carried
  | kept (link k : Nat)
  | own (k : Nat)
  | mask
  | atStart (i : Nat)
  | other
  deriving Repr, DecidableEq

structure PSeat where
  label : String
  /-- the number of the sending in the planner's list -/
  send : Nat
  /-- the group (link) and the moment, where the sending is a link's -/
  seg : Option (Nat × Nat)
  idx : Nat
  j : Nat
  t : Nat
  shape : OnBytes.OracleShape
  role : Role

def rootsBefore (dl : List Fmt.DeclaredRound) (k : Nat) : Nat := ((dl.take k).map (·.entry.roots)).sum

/-- The roles of the members of "link l, moment m", in frameSends' order. -/
def rolesOf (S : OnBytes.Params.ReqShape) (groups : List OnBytes.ReqGroup) (l m : Nat) : List Role :=
  let msgs := ((S.link[l]?).map (·.messages)).getD []
  let ownAt := (msgs.zipIdx.filter fun x => x.1.moment == m).map fun x => Role.own x.2
  if m != 0 then ownAt
  else
    let g := groups.getD l default
    (if 0 < l then [Role.carried] else []) ++ (g.born.toList.map fun b => Role.kept b.1 b.2) ++ ownAt ++
      [Role.mask] ++ (if l == 0 then (List.range S.atStart.length).map Role.atStart else [])

/-- "link l, moment m" read back off a label. -/
def segOf (groups moments : Nat) (label : String) : Option (Nat × Nat) :=
  (List.range groups).findSome? fun l => (List.range moments).findSome? fun m =>
    if label == s!"link {l}, moment {m}" then some (l, m) else none

def planSeats (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) : List PSeat :=
  let c := Z.made.proof.1
  let S := Z.first.shape
  let groups := (OnBytes.reqGroups S).toList
  c.sends.zipIdx.flatMap fun s =>
    match OnBytes.layTrees c.codes s.1.sent.toArray with
    | none => []
    | some lay =>
      let seg := segOf (groups.length + 1) 16 s.1.label
      let roles := match seg with
        | some (l, m) => rolesOf S groups l m
        | none => []
      (List.range s.1.sent.length).map fun i =>
        { label := s.1.label, send := s.2, seg := seg, idx := i,
          j := rootsBefore dl (s.1.entry - 1) + lay.tree.getD i 0, t := lay.part.getD i 0,
          shape := (s.1.sent.getD i default).shape, role := roles.getD i .other }

/-- The seats of another chain's oracle messages: no link, no role. The sendings' numbers are moved by 1000 * the chain's
number, so that no two chains share a key (keyOf). base: the trees of the chains in front. -/
def chainSeats (chain base : Nat) (c : Johnson.G.ChainSends) (dl : List Fmt.DeclaredRound) : List PSeat :=
  c.sends.zipIdx.flatMap fun s =>
    match OnBytes.layTrees c.codes s.1.sent.toArray with
    | none => []
    | some lay =>
      (List.range s.1.sent.length).map fun i =>
        { label := s!"chain {chain}, {s.1.label}", send := 1000 * chain + s.2, seg := none, idx := i,
          j := base + rootsBefore dl (s.1.entry - 1) + lay.tree.getD i 0, t := lay.part.getD i 0,
          shape := (s.1.sent.getD i default).shape, role := .other }

/-- The seats of all three chains of the proof file: the first chain's first. D: the three chains' declared rounds. -/
def planSeatsAll (Z : ProofFile.Pub) (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) : List PSeat :=
  let t₁ := rootsBefore D.1 D.1.length
  let t₂ := rootsBefore D.2.1 D.2.1.length
  planSeats Z D.1 ++ chainSeats 1 t₁ Z.made.proof.2.1 D.2.1 ++ chainSeats 2 (t₁ + t₂) Z.made.proof.2.2 D.2.2

/-- Each role's shape against the notice at its place; and as many roles as members. -/
def rolesFit (Z : ProofFile.Pub) (ps : List PSeat) : List String :=
  let S := Z.first.shape
  let groups := (OnBytes.reqGroups S).toList
  ps.filterMap fun p =>
    match p.seg, p.role with
    | some (l, _), .own k =>
      if (((S.link[l]?).bind (·.messages[k]?)).map (·.shape)) == some p.shape then none
      else some s!"{p.label}, message {p.idx}: own {k}: another shape"
    | some _, .kept l₀ k =>
      if (((S.link[l₀]?).bind (·.messages[k]?)).map fun m => (m.shape.code, m.shape.mainRows, m.shape.mainDeg)) ==
          some (p.shape.code, p.shape.mainRows, p.shape.mainDeg) then none
      else some s!"{p.label}, message {p.idx}: kept ({l₀}, {k}): other main rows"
    | some (l, _), .carried =>
      if (groups.getD l default).target.shape == p.shape then none
      else some s!"{p.label}, message {p.idx}: carried: another shape"
    | some _, .mask => if p.shape.answers == 0 && p.shape.mainRows == 0 then none
      else some s!"{p.label}, message {p.idx}: the mask has a sample or main rows"
    | some _, .atStart i => if ((S.atStart[i]?).map (·.shape)) == some p.shape then none
      else some s!"{p.label}, message {p.idx}: atStart {i}: another shape"
    | some _, .other => some s!"{p.label}, message {p.idx}: no role"
    | none, _ => none

/-- What a seat holds: an own message of a link (by link and number in the link's list), at the original and
at every kept copy alike; any other message by its sending and place there. -/
def keyOf (p : PSeat) : Nat × Nat × Nat :=
  match p.seg, p.role with
  | some (l, _), .own k => (0, l, k)
  | _, .kept l k => (0, l, k)
  | _, _ => (1, p.send, p.idx)

/-- **arr, off the plan**: the number, in the witness, of the message that tenant t of tree j holds: ONE NUMBER
FOR THE ORIGINAL AND ALL ITS KEPT COPIES. Beyond the list: the number of keys. -/
def arrOf (ps : List PSeat) (j t : Nat) : Nat :=
  let keys := (ps.map keyOf).eraseDups
  match ps.find? fun p => p.j == j && p.t == t with
  | some p => keys.idxOf (keyOf p)
  | none => keys.length

def seatsLines (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) : List String :=
  let ps := planSeats Z dl
  let bad := rolesFit Z ps
  let cnt (f : PSeat → Bool) : Nat := (ps.filter f).length
  [s!"PLAN-SEATS = oracle messages {ps.length} ; in links' sendings {cnt fun p => p.seg.isSome} ; carried " ++
    s!"{cnt fun p => p.role == .carried} ; kept copies {cnt fun p => match p.role with | .kept _ _ => true | _ => false} ; own " ++
    s!"{cnt fun p => match p.role with | .own _ => true | _ => false} ; fresh masks {cnt fun p => p.role == .mask} ; atStart " ++
    s!"{cnt fun p => match p.role with | .atStart _ => true | _ => false} ; others {cnt fun p => p.role == .other}",
   s!"ROLES-FIT = faults {bad.length} {bad.take 8}",
   (let kept := ps.filter fun p => match p.role with | .kept _ _ => true | _ => false
    let found := kept.filter fun p => ps.any fun q => (match q.role with | .own _ => true | _ => false) && keyOf q == keyOf p
    let seats := ps.map fun p => (p.j, p.t)
    s!"ARR = numbers {((ps.map keyOf).eraseDups).length} for {ps.length} seats ; kept copies whose original is found " ++
      s!"{found.length} of {kept.length} ; two oracle messages at one seat: {seats.length - seats.eraseDups.length} ; " ++
      s!"a copy and its original have one number: {(kept.filter fun p => ps.any fun q => (match q.role with | .own _ => true | _ => false) && arrOf ps q.j q.t == arrOf ps p.j p.t).length} of {kept.length}")] ++
  (ps.take 40).map fun p =>
    s!"SEAT = {p.label} ; message {p.idx} ; tree {p.j} tenant {p.t} ; answers {p.shape.answers} ; rows {p.shape.mainRows} | " ++
      s!"{p.shape.maskRows} ; {repr p.role}"

end P5T
