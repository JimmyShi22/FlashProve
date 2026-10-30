-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K4Seat.lean.
The rest of this head may differ from this file's text; where it does, the text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: K4's block (the feed-forward layers' own
rounds) at its
place in onlineDescription's first chain, seated at the public part's own members.
OBJECT. THE SEATED CONSTANT: ProofFile.k4Block x (Johnson/Desc/ProofFile/Lot/K4.lean) := K4.blockAtC { x.2 with k3Runs := true } with planOk := … && x.1, at a member x of
ProofFile.k4From Z G₀ G₀.built.toList 0 none, as it stands at F.first.links[2 g].hear[2], g < 12.
USER. K4's laws at the seated block; Meaning.Planes.block_planes | blockAtS_planes (Johnson/Meaning/PlanesBlock.lean | PlanesBlockAtS.lean) want the three premises on p.P | p.hp | p.g.
LETTERS. As in Johnson/IMR/K6Seat.lean; x: the lot's own pair (found, p): HANDED OUT BY ITS
MEMBERSHIP IN THE LOT's LIST and by p.link = 2 g.

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7' | G7'bits (Ladder.lean · Ladder/Bits.lean) hand every o: for these the in-scope halves are owed, at PublicCut (Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean)).

  K4At · k4From_mem every pair that k4From lays stems from a link X of kind 0 in the list, at that link's number: P := G.W.layers, hp := G.W.G[X.g], g := X.g, piece 3, the name X.name ++ ":3".
  k4_seated         for every x ∈ k4From …: p.P = G₀.W.layers · G₀.W.G[p.g]? = some p.hp, AND THE THREE PREMISES OF Meaning.Planes.block_planes | blockAtS_planes, to the letter:
                    p.P.tails = tailsOf p.P.y · plansG p.P = ok G₀.W.G · G₀.W.G[p.g]? = some p.hp. No premise on scope.
  k4_seated_scope   in the goals' scope besides: p.g < 12 · p.link = 2 * p.g · p.piece = 3 · the name is "G" ++ toString p.g ++ ":3".
  k4_of             at an opening's letters, for every g < 12: link 2 g's third block in front of the batching IS seatedAs ProofFile.sameReply (k4Block x) b.name ⟨1, some (2 g), 3, K4⟩: ALONE.
  k4_alone_z        the same in one piece, from onlineDescription's value.
  k4_yes            b.decide s rs gs = ok t ↔ (K4.blockAtS { p with k3Runs := true }).decide s rs gs = ok t ∧ t.failed = none ∧ sameReply s t = true.

WHO PAYS THE PREMISES: as in Johnson/IMR/K6Seat.lean: that onlineDescription returns in scope is a premise.
What is not claimed. That x.1 = true (a message was found at the link's first place): where it is false the seated block's planOk is false, and F.planOk with it. Nothing on the runs' texts. No soundness.
-/
import Johnson.IMR.LaidFirst
import Johnson.IMR.SeatOpen
import Johnson.IMR.Subs
import Johnson.Goal.Meaning.Pub34Scope

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open ProofFile (Cl)

/-- What a parameter record of K4's lot has of a link X at number l. -/
structure K4At (G : ProofFile.Ground) (p : OnBytes.Desc.First.K4.Par) (X : LinkH) (l : ℕ) : Prop where
  kind : X.kind = 0
  hp : G.W.G[X.g]? = some p.hp
  P : p.P = G.W.layers
  g : p.g = X.g
  link : p.link = l
  piece : p.piece = 3
  name : p.name = s!"{X.name}:3"

/-- **Every pair that k4From lays stems from a link of kind 0, at its number.** -/
theorem k4From_mem (Z : ProofFile.Pub) (G : ProofFile.Ground) : ∀ (L : List LinkH) (l : ℕ) (last : Option String)
    (x : Bool × OnBytes.Desc.First.K4.Par), x ∈ ProofFile.k4From Z G L l last →
      ∃ j X, L[j]? = some X ∧ K4At G x.2 X (l + j)
  | [], _, _, x, h => by
    simp [ProofFile.k4From] at h
  | X :: rest, l, last, x, h => by
    unfold ProofFile.k4From at h
    split at h
    · rename_i hk
      have hk0 : X.kind = 0 := by simpa using hk
      rcases List.mem_append.1 h with h1 | h2
      · split at h1
        · rename_i hp hg
          obtain rfl := List.mem_singleton.1 h1
          exact ⟨0, X, rfl, hk0, hg, rfl, rfl, rfl, rfl, rfl⟩
        · cases h1
      · obtain ⟨j, Y, e, K⟩ := k4From_mem Z G rest (l + 1) _ x h2
        refine ⟨j + 1, Y, e, K.kind, K.hp, K.P, K.g, ?_, K.piece, K.name⟩
        rw [K.link]
        omega
    · obtain ⟨j, Y, e, K⟩ := k4From_mem Z G rest (l + 1) _ x h
      refine ⟨j + 1, Y, e, K.kind, K.hp, K.P, K.g, ?_, K.piece, K.name⟩
      rw [K.link]
      omega

/-- The same at the lot's own list. -/
theorem k4List_mem {Z : ProofFile.Pub} {G : ProofFile.Ground} {x : Bool × OnBytes.Desc.First.K4.Par}
    (h : x ∈ ProofFile.k4From Z G G.built.toList 0 none) : ∃ j X, G.built[j]? = some X ∧ K4At G x.2 X j := by
  obtain ⟨j, X, e, K⟩ := k4From_mem Z G _ 0 none x h
  refine ⟨j, X, ?_, ?_⟩
  · rw [← Array.getElem?_toList]
    exact e
  · rw [Nat.zero_add] at K
    exact K

/-- **K4's PLACES ARE SEATED AT THE PUBLIC PART's OWN MEMBERS.** -/
theorem k4_seated {pol lay KL : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    {x : Bool × OnBytes.Desc.First.K4.Par} (hx : x ∈ ProofFile.k4From Z G₀ G₀.built.toList 0 none) :
    x.2.P = G₀.W.layers ∧ x.2.P.tails = Layer.tailsOf x.2.P.y ∧ Layer.plansG x.2.P = .ok G₀.W.G ∧
      G₀.W.G[x.2.g]? = some x.2.hp := by
  have hX := ground_publicK hZ hG
  obtain ⟨j, X, -, K⟩ := k4List_mem hx
  obtain ⟨-, hT, -, -, hPl⟩ := Meaning.P34.more_of_public hX
  refine ⟨K.P, ?_, ?_, ?_⟩
  · rw [K.P]
    exact hT
  · rw [K.P]
    exact hPl
  · rw [K.g]
    exact K.hp

/-- **In the goals' scope: which place, which group.** -/
theorem k4_seated_scope {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G₀ : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    {x : Bool × OnBytes.Desc.First.K4.Par} (hx : x ∈ ProofFile.k4From Z G₀ G₀.built.toList 0 none) :
    x.2.g < 12 ∧ x.2.link = 2 * x.2.g ∧ x.2.piece = 3 ∧
      x.2.name = s!"{"G" ++ toString x.2.g}:3" := by
  obtain ⟨j, X, e, K⟩ := k4List_mem hx
  obtain ⟨sz, -⟩ := ground_gets hS hR hZ hG
  obtain ⟨nam, l24, e24, k24, -⟩ := ground_named hS hR hZ hG
  have hj : j < 25 := by
    rw [← sz]
    exact (Array.getElem?_eq_some_iff.1 e).1
  by_cases h24 : j = 24
  · subst h24
    obtain rfl : l24 = X := Option.some.inj (e24.symm.trans e)
    rw [K.kind] at k24
    cases k24
  · obtain ⟨l, l', a, ka, ga, Na, b, kb, gb, Nb⟩ := nam (j / 2) (by omega)
    by_cases he : j % 2 = 0
    · have ej : 2 * (j / 2) = j := by omega
      rw [ej] at a
      obtain rfl : l = X := Option.some.inj (a.symm.trans e)
      have eg : x.2.g = j / 2 := K.g.trans ga
      refine ⟨by omega, by rw [K.link]; omega, K.piece, ?_⟩
      rw [K.name, Na.name, eg]
    · have ej : 2 * (j / 2) + 1 = j := by omega
      rw [ej] at b
      obtain rfl : l' = X := Option.some.inj (b.symm.trans e)
      rw [K.kind] at kb
      cases kb

/-- K4's address at group g. -/
abbrev k4Place (g : ℕ) : Place := { chain := 1, link := some (2 * g), piece := 3, kind := .K4 }

/-- **K4 AT EACH LAYERS' LINK: THE LOT's SEATED BLOCK, ALONE: AT AN OPENING's OWN LETTERS.** -/
theorem k4_of {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ g < 12, ∃ (Lk : Link S Cl) (b : Block S Cl) (x : Bool × OnBytes.Desc.First.K4.Par),
      c.links[2 * g]? = some Lk ∧ Lk.hear[2]? = some b ∧
      x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none ∧
      LaidAlone ProofFile.sameReply b (ProofFile.k4Block x) b.name (k4Place g) ∧
      x.2.link = 2 * g ∧ x.2.g = g ∧ x.2.P = Bs.G₀.W.layers ∧ Bs.G₀.W.G[g]? = some x.2.hp ∧
      x.2.P.tails = Layer.tailsOf x.2.P.y ∧ Layer.plansG x.2.P = .ok Bs.G₀.W.G := by
  intro g hg
  have hZ := O.pub
  have hG := O.blank
  have hk : (kindsBeforeBatching .layers (2 * g == 0))[2]? = some KindName.K4 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
    chain_hear_alone O.made O.places O.chain (2 * g) .layers (subs_at hS hR hZ hG hg) 2 .K4 hk
      (by decide) (by decide) (by decide)
  obtain rfl : L = ProofFile.k4Lot Z := lot_of_kind hL hb' (by rw [ep]; rfl)
  have hb'' : b' ∈ (ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none).map ProofFile.k4Block := by
    rcases blocks_mem hb' with ⟨y, hy, -⟩ | h
    · exact nomatch hy
    · exact h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb''
  obtain ⟨eP, hT, hPl, hgp⟩ := k4_seated hZ hG hx
  obtain ⟨-, hlk, -, -⟩ := k4_seated_scope hS hR hZ hG hx
  have el : x.2.link = 2 * g := by
    have e : (some x.2.link : Option ℕ) = some (2 * g) := congrArg Place.link ep
    exact Option.some.inj e
  have eg : x.2.g = g := by omega
  rw [eg] at hgp
  have hla' : LaidAlone ProofFile.sameReply b (ProofFile.k4Block x) b.name (k4Place g) := by
    rw [alone_name hla]
    exact hla
  exact ⟨Lk, b, x, e1, e2, hx, hla', el, eg, eP, hgp, hT, hPl⟩

/-- **The same in one piece, from onlineDescription's value.** -/
theorem k4_alone_z {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ (X : Verify.Public) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat)
        (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧ publicOf P.pol P.KL (some lay) = .ok X ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧ G₀.W = X ∧
      ProofFile.onlineSharedChain Z = some A ∧ ProofFile.onlineLastChain Z = some B ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ g < 12, ∃ (Lk : Link S Cl) (b : Block S Cl) (x : Bool × OnBytes.Desc.First.K4.Par),
        c.links[2 * g]? = some Lk ∧ Lk.hear[2]? = some b ∧
        x ∈ ProofFile.k4From Z G₀ G₀.built.toList 0 none ∧
        LaidAlone ProofFile.sameReply b (ProofFile.k4Block x) b.name (k4Place g) ∧
        x.2.link = 2 * g ∧ x.2.g = g ∧ x.2.P = X.layers ∧ X.G[g]? = some x.2.hp ∧
        x.2.P.tails = Layer.tailsOf x.2.P.y ∧ Layer.plansG x.2.P = .ok X.G := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := seat_open hF
  exact ⟨Bs.G₀.W, Z, Bs.G₀, c, A, B, O.pub, O.public, O.blank, rfl, O.shared, O.second, O.desc,
    k4_of hS hR O⟩

/-- **The seated block's yes is K4's own block's yes at the carried record**, with no mark behind it and the reply as it was. -/
theorem k4_yes {b : Block S Cl} {x : Bool × OnBytes.Desc.First.K4.Par} {name : String} {g : ℕ}
    (h : LaidAlone ProofFile.sameReply b (ProofFile.k4Block x) name (k4Place g)) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) :
    b.decide s rs gs = .ok t ↔
      (OnBytes.Desc.First.K4.blockAtS { x.2 with k3Runs := true }).decide s rs gs = .ok t ∧
        t.failed = none ∧ ProofFile.sameReply s t = true :=
  yes_alone h (fun e => nomatch e) s t rs gs

end IM

#print axioms IM.k4From_mem
#print axioms IM.k4_seated
#print axioms IM.k4_seated_scope
#print axioms IM.k4_of
#print axioms IM.k4_alone_z
#print axioms IM.k4_yes
