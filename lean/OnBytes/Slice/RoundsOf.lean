-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RoundsOf.lean: what the rounds of the batching and the proximity test send and draw.

The link is the format's protocol between two stored tables (OnBytes/Slice/README.md has the
vocabulary). The rounds after its first five are of seven kinds, which the format defines from the
sizes: `rEps`, `rTwo`, `rSeed`, `rCs`, `rLambda`, `rBase` (Fmt/M1Plan.lean) and `rBatN`
(Fmt/M2Plan.lean). A theorem on a written round needs to know how many elements the prover sends,
how many elements and positions the verifier draws, and that nothing else is drawn. This file says
it once, in the notions of OnBytes/Slice/Draws.lean, so that one hypothesis on a written round,
`IsRd d r`, gives all of it.

Main definitions.
 `nS`         the number of elements of the extension field among the items of a prover message.
 `IsRd d r`   the written round d has the entry, the kind and the items of the format's round r.
 `SendsDraws d ns ne np a`   d sends ns elements; it draws ne elements and np positions below 2^a,
              and nothing else.
 `gMix`       the typed values of a round that draws elements and positions.
Main theorems.
 `rEps_sd`, `rTwo_sd`, `rSeed_sd`, `rCs_sd`, `rLambda_sd`, `rBase_sd`, `rBatN_sd`
              the numbers of each of the seven rounds.
 `rSeed_nz`   a seed's factor is drawn other than 0.
 `rvOf_sent`, `rvOf_els`, `rvOf_poss`
              what the decision reads of a written round is what was sent and the typed values that
              were drawn.
 `SendsDraws.next`
              the decision's test of a round's sizes does not refuse.
 `SendsDraws.gVec_inj`, `rSeed_gSeed_inj`, `SendsDraws.gLoc_inj`, `SendsDraws.gMix_inj`
              the typed values are determined by their reading as elements, as a seed, as positions,
              as both.

Not claimed. Nothing on the trees that a round sends or opens, nor on the test of work. Nothing on
which rounds a given description has.
-/
import Fmt.M1Plan
import Fmt.M2Plan
import OnBytes.Slice.DrawsOf
import OnBytes.Slice.Stage

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-! ## The notions -/

/-- The number of elements of the extension field among the items of a prover message. -/
def nS : List Fmt.Item → ℕ
  | [] => 0
  | .e :: l => nS l + 1
  | .answer :: l => nS l + 1
  | _ :: l => nS l

/-- The written round d has the entry, the kind and the items of the format's round r. -/
structure IsRd (d : PQ.RD) (r : Fmt.Round) : Prop where
  entry : d.entry = r.entry
  kind : d.kind = r.kind
  items : d.items = r.items

/-- The written round d sends ns elements; it draws ne elements and np positions below 2^a, and
nothing else. Its entry's `logN` is at most 64. -/
structure SendsDraws (d : PQ.RD) (ns ne np a : ℕ) : Prop where
  sent : nS d.items = ns
  plain : PlainDraws (Fmt.dsOf d.entry d.kind)
  els : nE (Fmt.dsOf d.entry d.kind) = ne
  poss : nP (Fmt.dsOf d.entry d.kind) = np
  allPos : AllPos a (Fmt.dsOf d.entry d.kind)
  logN : d.entry.logN ≤ 64

/-- Both rounds have the same list of draws. -/
theorem IsRd.dsOf {d : PQ.RD} {r : Fmt.Round} (h : IsRd d r) :
    Fmt.dsOf d.entry d.kind = Fmt.dsOf r.entry r.kind := by
  rw [h.entry, h.kind]

/-- A list of n items `e` holds n elements. -/
theorem nS_replicate_e : ∀ n, nS (List.replicate n Fmt.Item.e) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (nS_replicate_e n)

/-! ## The seven rounds -/

/-- The numbers of a round that is neither a sealing nor one of seeds, and draws no matrix
entries. -/
theorem sendsDraws_of {d : PQ.RD} {r : Fmt.Round} (h : IsRd d r) (ht : r.entry.trits = 0)
    (hk : r.kind ≠ .sealed) (hs : r.kind ≠ .seeds) (hz : r.entry.drawNZ ≤ r.entry.drawE)
    (hl : r.entry.logN ≤ 64) :
    SendsDraws d (nS r.items) r.entry.drawE r.entry.poss r.entry.logN where
  sent := by rw [h.items]
  plain := by rw [h.dsOf]; exact plain_dsOf _ _ ht hk
  els := by rw [h.dsOf]; exact nE_dsOf _ _ hz hs
  poss := by rw [h.dsOf]; exact nP_dsOf _ _
  allPos := by rw [h.dsOf]; exact allPos_dsOf _ _
  logN := by rw [h.entry]; exact hl

/-- The round that joins a hiding sum to a claim: one element is sent, one is drawn. -/
theorem rEps_sd {d : PQ.RD} {name : String} (h : IsRd d (Fmt.M1.rEps name)) :
    SendsDraws d 1 1 0 0 :=
  sendsDraws_of h rfl (by decide : Fmt.Kind.join ≠ .sealed) (by decide : Fmt.Kind.join ≠ .seeds)
    (Nat.zero_le 1) (Nat.zero_le 64)

/-- A round of a sum: two coefficients are sent, one element is drawn. -/
theorem rTwo_sd {d : PQ.RD} {name : String} (h : IsRd d (Fmt.M1.rTwo name)) :
    SendsDraws d 2 1 0 0 :=
  sendsDraws_of h rfl (by decide : Fmt.Kind.elems ≠ .sealed) (by decide : Fmt.Kind.elems ≠ .seeds)
    (Nat.zero_le 1) (Nat.zero_le 64)

/-- The sending of a tree: no element is sent; the seed of the stage's sample is drawn. -/
theorem rSeed_sd {d : PQ.RD} {s : Fmt.M1.Stage} (h : IsRd d (Fmt.M1.rSeed s)) :
    SendsDraws d 0 (s.na + 1) 0 0 where
  sent := by rw [h.items]; rfl
  plain := by
    rw [h.dsOf]
    exact plain_dsOf _ _ rfl (by decide : Fmt.Kind.seeds ≠ .sealed)
  els := by rw [h.dsOf]; exact nE_dsOf_seed (Fmt.M1.rSeed s).entry rfl (Nat.le_add_left 1 s.na)
  poss := by rw [h.dsOf]; exact nP_dsOf (Fmt.M1.rSeed s).entry _
  allPos := by rw [h.dsOf]; exact allPos_dsOf (Fmt.M1.rSeed s).entry _
  logN := by rw [h.entry]; exact Nat.zero_le 64

/-- The factor of a seed, its last element, is drawn other than 0. -/
theorem rSeed_nz {d : PQ.RD} {s : Fmt.M1.Stage} (h : IsRd d (Fmt.M1.rSeed s)) :
    IsNZ (Fmt.dsOf d.entry d.kind) s.na := by
  rw [h.dsOf]
  exact isNZ_dsOf_seed (Fmt.M1.rSeed s).entry rfl

/-- The code switch: one answer is sent; one element and the stage's positions are drawn. -/
theorem rCs_sd {d : PQ.RD} {work tree W : ℕ} {s : Fmt.M1.Stage}
    (h : IsRd d (Fmt.M1.rCs work s tree W)) (ha : s.C.a ≤ 64) : SendsDraws d 1 1 s.t s.C.a :=
  sendsDraws_of h rfl (by decide : Fmt.Kind.positions ≠ .sealed)
    (by decide : Fmt.Kind.positions ≠ .seeds) (Nat.zero_le 1) ha

/-- The first round of the base case: one element is sent, one is drawn. -/
theorem rLambda_sd {d : PQ.RD} (h : IsRd d Fmt.M1.rLambda) : SendsDraws d 1 1 0 0 :=
  sendsDraws_of h rfl (by decide : Fmt.Kind.elems ≠ .sealed) (by decide : Fmt.Kind.elems ≠ .seeds)
    (Nat.zero_le 1) (Nat.zero_le 64)

/-- The last round: the last stage's messages and tails are sent; its positions are drawn. -/
theorem rBase_sd {d : PQ.RD} {work tree : ℕ} {s : Fmt.M1.Stage}
    (h : IsRd d (Fmt.M1.rBase work s tree)) (ha : s.C.a ≤ 64) :
    SendsDraws d (s.C.l + s.Z.l + s.C.r + s.Z.r) 0 s.t s.C.a := by
  have h0 : SendsDraws d (nS (List.replicate (Fmt.M1.clearN s) Fmt.Item.e)) 0 s.t s.C.a :=
    sendsDraws_of h rfl (by decide : Fmt.Kind.positions ≠ .sealed)
      (by decide : Fmt.Kind.positions ≠ .seeds) (Nat.le_refl 0) ha
  exact ⟨h0.sent.trans (nS_replicate_e _), h0.plain, h0.els, h0.poss, h0.allPos, h0.logN⟩

/-- The batching: nothing is sent, one element is drawn. -/
theorem rBatN_sd {d : PQ.RD} {rows : ℕ} (h : IsRd d (Fmt.M2.rBatN rows)) : SendsDraws d 0 1 0 0 :=
  sendsDraws_of h rfl (by decide : Fmt.Kind.elems ≠ .sealed) (by decide : Fmt.Kind.elems ≠ .seeds)
    (Nat.zero_le 1) (Nat.zero_le 64)

/-! ## What the decision reads of a written round -/

/-- The elements among the items read, in the field. -/
theorem sentOf_map : ∀ l : List Fmt.ItemValue, (Fmt.M1.sentOf l).map toE =
    l.filterMap fun g =>
      match g with
      | .e x => some (toE x)
      | .answer x => some (toE x)
      | _ => none
  | [] => rfl
  | .e x :: l => congrArg (toE x :: ·) (sentOf_map l)
  | .answer x :: l => congrArg (toE x :: ·) (sentOf_map l)
  | .f _ :: l => sentOf_map l
  | .word _ :: l => sentOf_map l
  | .root _ :: l => sentOf_map l

/-- The decision reads as many elements as sent as the list of items has. -/
theorem sentOf_gots_length : ∀ (l : List Fmt.Item) (x : PQ.PlainOf l),
    (Fmt.M1.sentOf (PQ.PlainOf.gots l x)).length = nS l
  | [], _ => rfl
  | .root :: l, x => sentOf_gots_length l x
  | .f :: l, (x : UInt64 × PQ.PlainOf l) => sentOf_gots_length l x.2
  | .word :: l, (x : UInt64 × PQ.PlainOf l) => sentOf_gots_length l x.2
  | .e :: l, (x : Fmt.Ext × PQ.PlainOf l) => congrArg (· + 1) (sentOf_gots_length l x.2)
  | .answer :: l, (x : Fmt.Ext × PQ.PlainOf l) => congrArg (· + 1) (sentOf_gots_length l x.2)

section
variable (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal)

/-- The elements that the decision reads as sent are the message's. -/
theorem rvOf_sent : (rvOf d m c).sent.map toE = ansOf d m := sentOf_map _

/-- The elements that the decision reads as drawn are the typed ones. -/
theorem rvOf_els : (rvOf d m c).els.map toE = elemsV _ (valsOf d c) := collect_elems _ _

/-- The positions that the decision reads as drawn are the typed ones. -/
theorem rvOf_poss : (rvOf d m c).poss = possV _ (valsOf d c) := collect_poss _ _

end

namespace SendsDraws
variable {d : PQ.RD} {ns ne np a : ℕ} (h : SendsDraws d ns ne np a)
  (m : (wRound d).Msg) (c : (wRound d).Chal)
include h

/-- The decision reads ns elements as sent. -/
theorem sent_length : (rvOf d m c).sent.length = ns :=
  (sentOf_gots_length d.items _).trans h.sent

/-- The decision reads ne elements as drawn. -/
theorem els_length : (rvOf d m c).els.length = ne := by
  have h1 : ((rvOf d m c).els.map toE).length = ne := by
    rw [rvOf_els, elemsV_length]
    exact h.els
  rwa [List.length_map] at h1

/-- The decision reads np positions as drawn. -/
theorem poss_length : (rvOf d m c).poss.length = np := by
  rw [rvOf_poss, possV_length]
  exact h.poss

/-- Every position that the decision reads as drawn is below 2^a. -/
theorem poss_lt : ∀ x ∈ (rvOf d m c).poss, x < 2 ^ a := by
  rw [rvOf_poss]
  exact possV_lt a _ h.allPos _

/-- The decision's test of a round's sizes does not refuse. -/
theorem next (rs : Fmt.M1.Rs) :
    Fmt.M1.nextN ns ne np (rvOf d m c :: rs) = some (rvOf d m c, rs) := by
  have hsz : ((rvOf d m c).sent.length == ns && (rvOf d m c).els.length == ne &&
      (rvOf d m c).poss.length == np) = true := by
    rw [h.sent_length m c, h.els_length m c, h.poss_length m c]
    simp only [beq_self_eq_true, Bool.and_self]
  exact if_pos hsz

end SendsDraws

/-! ## The typed values as verifier messages of the library -/

/-- Typed values with the same reading as n elements have the same elements. -/
theorem elemsV_of_gVec (n : ℕ) (ds : List Fmt.Draw) (hE : nE ds = n) (v w : Vals .two ds)
    (h : gVec n ds v = gVec n ds w) : elemsV ds v = elemsV ds w :=
  list_ext_getD 0 ((elemsV_length ds v).trans (elemsV_length ds w).symm) fun i hi =>
    congrFun h ⟨i, by rw [← hE, ← elemsV_length ds v]; exact hi⟩

/-- Typed values with the same reading as t positions have the same positions. -/
theorem possV_of_gLoc (a t : ℕ) (ds : List Fmt.Draw) (hP : nP ds = t) (hA : AllPos a ds)
    (v w : Vals .two ds) (h : (gLoc a t 0 ds v).1 = (gLoc a t 0 ds w).1) :
    possV ds v = possV ds w :=
  list_ext_getD 0 ((possV_length ds v).trans (possV_length ds w).symm) fun i hi => by
    have hi' : i < t := by rw [← hP, ← possV_length ds v]; exact hi
    have key : (possV ds v).getD i 0 % 2 ^ a = (possV ds w).getD i 0 % 2 ^ a :=
      congrArg Fin.val (congrFun h ⟨i, hi'⟩)
    rwa [Nat.mod_eq_of_lt (getD_lt a ds hA v i), Nat.mod_eq_of_lt (getD_lt a ds hA w i)] at key

/-- The typed values, read as n elements and t positions below 2^a. -/
def gMix (n a t : ℕ) (ds : List Fmt.Draw) (v : Vals .two ds) :
    (Fin n → GE) × (Fin t → Fin (2 ^ a)) :=
  (gVec n ds v, (gLoc a t 0 ds v).1)

/-- Typed values of a list of n elements and t positions below 2^a, and nothing else, are determined
by their reading as elements and positions. -/
theorem gMix_inj (n a t : ℕ) (ds : List Fmt.Draw) (hp : PlainDraws ds) (hE : nE ds = n)
    (hP : nP ds = t) (hA : AllPos a ds) : Function.Injective (gMix n a t ds) := fun v w h =>
  vals_inj ds hp v w (elemsV_of_gVec n ds hE v w (congrArg Prod.fst h))
    (possV_of_gLoc a t ds hP hA v w (congrArg Prod.snd h))

/-- At a round that draws elements alone the typed values are determined by their reading as
elements. -/
theorem SendsDraws.gVec_inj {d : PQ.RD} {ns ne a : ℕ} (h : SendsDraws d ns ne 0 a) :
    Function.Injective (gVec ne (Fmt.dsOf d.entry d.kind)) :=
  OnBytes.Slice.gVec_inj ne _ h.plain h.els h.poss

/-- At the sending of a tree the typed values are determined by their reading as a seed. -/
theorem rSeed_gSeed_inj {d : PQ.RD} {s : Fmt.M1.Stage} (h : IsRd d (Fmt.M1.rSeed s)) :
    Function.Injective (gSeed s.na (Fmt.dsOf d.entry d.kind)) :=
  gSeed_inj s.na _ (rSeed_sd h).plain (rSeed_sd h).els (rSeed_sd h).poss (rSeed_nz h)

/-- At a round that draws positions alone the typed values are determined by their reading as two
lists of positions. -/
theorem SendsDraws.gLoc_inj {d : PQ.RD} {ns t0 t1 a : ℕ} (h : SendsDraws d ns 0 (t0 + t1) a) :
    Function.Injective (gLoc a t0 t1 (Fmt.dsOf d.entry d.kind)) :=
  OnBytes.Slice.gLoc_inj a t0 t1 _ h.plain h.els h.poss h.allPos

/-- At a round that draws elements and positions the typed values are determined by their reading as
both. -/
theorem SendsDraws.gMix_inj {d : PQ.RD} {ns ne np a : ℕ} (h : SendsDraws d ns ne np a) :
    Function.Injective (gMix ne a np (Fmt.dsOf d.entry d.kind)) :=
  OnBytes.Slice.gMix_inj ne a np _ h.plain h.els h.poss h.allPos

end OnBytes.Slice

#print axioms OnBytes.Slice.sendsDraws_of
#print axioms OnBytes.Slice.rEps_sd
#print axioms OnBytes.Slice.rTwo_sd
#print axioms OnBytes.Slice.rSeed_sd
#print axioms OnBytes.Slice.rSeed_nz
#print axioms OnBytes.Slice.rCs_sd
#print axioms OnBytes.Slice.rLambda_sd
#print axioms OnBytes.Slice.rBase_sd
#print axioms OnBytes.Slice.rBatN_sd
#print axioms OnBytes.Slice.rvOf_sent
#print axioms OnBytes.Slice.rvOf_els
#print axioms OnBytes.Slice.rvOf_poss
#print axioms OnBytes.Slice.SendsDraws.sent_length
#print axioms OnBytes.Slice.SendsDraws.els_length
#print axioms OnBytes.Slice.SendsDraws.poss_length
#print axioms OnBytes.Slice.SendsDraws.next
#print axioms OnBytes.Slice.SendsDraws.poss_lt
#print axioms OnBytes.Slice.SendsDraws.gVec_inj
#print axioms OnBytes.Slice.rSeed_gSeed_inj
#print axioms OnBytes.Slice.SendsDraws.gLoc_inj
#print axioms OnBytes.Slice.SendsDraws.gMix_inj
