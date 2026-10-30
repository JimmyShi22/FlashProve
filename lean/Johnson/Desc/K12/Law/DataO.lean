-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.MemberOMore
import Johnson.Desc.K12.Law.BatOneMade
import Johnson.Desc.K12.Law.DataOf
/-
Johnson/Desc/K12/Law/DataO.lean: THE STRETCH's DATA AND THE TREES' DEPTHS AT THE PROXIMITY TEST O OF THE SMALL STORED PROOF OF A BUILD THAT DOES NOT SHIP, MADE BY HAND OFF THE PLAN piO AND THE RECORD's BOOK; closed facts by the kernel. Definitions, statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  rdsO · wsO: the block's declared rounds; the written rounds. r0O | rtO · w0O | lO: their heads and tails. rdsO_cons · wsO_cons · written_O · len_O · stored_O.
  allO t₁: EIGHT trees with their numbers over the file and their depths: the five of the record's book (book_O: the depths are the book's own) and the three that the test sends (trees_O).
  stO num t₁ key: the stretch as the maker's StageD: base t₁ + 5.
  depth_O: under num (.own n) = t₁ + n: the depth of each declared opening's tree is the declared one.
  chain_O: the place's chain is there, at the Johnson letters and the radii rO, with as many rounds as lO. cO: that chain as a term; cO_eq · cO_rds.
  ds_O · log_O · payPub_O: "BAT"'s draws and logN; PayPub at 768.
THESE DATA ARE NO DESCRIPTION's. t₁ (how many trees the first chain sends) is free on purpose.

-/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace H2K.Member
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (WR writtenOf chainFrom Letters sgOf pub_of_ok)
open H2K.Made (wr)

def rdsO : List Fmt.DeclaredRound := (proximityTestKind guardedProximityTestParts piO : Block T12 Unit).rounds
def wsO : List WR := (writtenOf piO.nums).getD []
def r0O : Fmt.DeclaredRound := ⟨{ Fmt.M1.rBat.entry with rows := piO.nums.rows }, [], []⟩
def rtO : List Fmt.DeclaredRound := rdsO.tail
def w0O : WR := wr r0O .elems none
def lO : List WR := wsO.tail
def aO : Fmt.M1.Stage := piO.nums.stages.headD default
def restO : List Fmt.M1.Stage := piO.nums.stages.tail

theorem stages_O : piO.nums.stages = aO :: restO := rfl
theorem wsO_cons : wsO = w0O :: lO := by decide +kernel
theorem rdsO_cons : rdsO = r0O :: rtO := by decide +kernel

theorem written_O : writtenOf piO.nums = some (w0O :: lO) := by
  obtain ⟨w0, w, hw⟩ := H2K.Made.written_of_planOk guardedProximityTestParts piO member_O.2.2.1
  have h : wsO = w0 :: w := by
    unfold wsO
    rw [hw]
    rfl
  rw [hw, ← h, wsO_cons]

theorem len_O : lO.length = rtO.length := by decide +kernel

theorem stored_O : ∀ r ∈ rdsO, r.stored = [] := by
  have h : (rdsO.all fun r => r.stored.isEmpty) = true := by decide +kernel
  intro r hr
  exact List.isEmpty_iff.1 (List.all_eq_true.1 h r hr)

theorem opens_O : (rdsO.flatMap (·.opens)).map (fun o => (o.1.a, o.2)) =
    [(18, .own 1), (13, .own 2), (13, .own 5), (14, .own 6), (15, .own 7)] := by decide +kernel

theorem trees_O : (treeW wsO 0).map (·.a) = some 13 ∧ (treeW wsO 1).map (·.a) = some 14 ∧
    (treeW wsO 2).map (·.a) = some 15 := by decide +kernel

/-- The depths of the five trees of the record's book. -/
theorem book_O : tO.book.trees.toList.map (·.shape.logN) = [17, 18, 13, 14, 14] := by
  decide +kernel

/-- Eight trees: the book's five, and the three that the test sends. -/
def allO (t₁ : ℕ) : List LeftT :=
  [⟨t₁, 17⟩, ⟨t₁ + 1, 18⟩, ⟨t₁ + 2, 13⟩, ⟨t₁ + 3, 14⟩, ⟨t₁ + 4, 14⟩, ⟨t₁ + 5, 13⟩, ⟨t₁ + 6, 14⟩,
    ⟨t₁ + 7, 15⟩]

/-- The first five depths are the book's own (logN: the depth that the law's W0 reads of the book by
logAt). -/
theorem allO_book (t₁ : ℕ) :
    ((allO t₁).take 5).map (·.a) = tO.book.trees.toList.map (·.shape.logN) := by
  rw [book_O]
  rfl

def stO (num : Fmt.TreeSource → ℕ) (t₁ : ℕ) (key : ℕ → ℕ) : StageD :=
  ⟨0, t₁ + 5, allO t₁, rdtOf num w0O r0O :: dataOf num lO rtO, key, allO t₁⟩

theorem data_O (num : Fmt.TreeSource → ℕ) :
    rdtOf num w0O r0O :: dataOf num lO rtO = dataOf num wsO rdsO := by
  rw [wsO_cons, rdsO_cons]
  rfl

theorem depth_O (num : Fmt.TreeSource → ℕ) (t₁ : ℕ) (key : ℕ → ℕ) (hnum : ∀ n, num (.own n) = t₁ + n) :
    ∀ r ∈ rdsO, ∀ o ∈ r.opens, (stO num t₁ key).depth (num o.2) = some o.1.a := by
  intro r hr o ho
  have hm : (o.1.a, o.2) ∈ (rdsO.flatMap (·.opens)).map (fun o => (o.1.a, o.2)) :=
    List.mem_map.2 ⟨o, List.mem_flatMap.2 ⟨r, hr, ho⟩, rfl⟩
  rw [opens_O] at hm
  have hl : wsO.length = rdsO.length := by
    rw [wsO_cons, rdsO_cons, List.length_cons, List.length_cons, len_O]
  have hown : ∀ n, (stO num t₁ key).depth (t₁ + 5 + n) = (treeW wsO n).map (·.a) := by
    intro n
    unfold StageD.depth
    have h1 : ¬ t₁ + 5 + n < (stO num t₁ key).base := by
      show ¬ t₁ + 5 + n < t₁ + 5
      omega
    rw [if_neg h1]
    show (treeShT (rdtOf num w0O r0O :: dataOf num lO rtO) (t₁ + 5 + n - (t₁ + 5))).map (·.a) = _
    rw [data_O, treeSh_dataOf num wsO rdsO _ hl, Nat.add_sub_cancel_left]
  obtain ⟨g0, g1, g2⟩ := trees_O
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨ha, hs⟩ | ⟨ha, hs⟩ | ⟨ha, hs⟩ | ⟨ha, hs⟩ | ⟨ha, hs⟩
  · rw [hs, hnum, ha]
    simp [StageD.depth, stO, allO]
  · rw [hs, hnum, ha]
    simp [StageD.depth, stO, allO]
  · rw [hs, hnum, ha]
    exact (hown 0).trans g0
  · rw [hs, hnum, ha]
    exact (hown 1).trans g1
  · rw [hs, hnum, ha]
    exact (hown 2).trans g2

/-- The place's chain, at the Johnson letters and the radii rO. -/
theorem chain_O : ∃ c : OnBytes.Slice.Chain (sgOf aO),
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => rO s.st) restO aO lO = some c ∧
      c.rds = lO.map WR.rd := by
  obtain ⟨a, rest, w0, l, c, hs, hw, hc, hr, _⟩ :=
    pub_of_ok (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => rO s.st) piO tO.st.codes
      member_O.2.2.2.2.2.2.2.2.2.1
  obtain ⟨rfl, rfl⟩ := List.cons.inj (stages_O.symm.trans hs)
  obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (written_O.symm.trans hw))
  exact ⟨c, hc, hr⟩

/-- The place's chain as a term. -/
noncomputable def cO : OnBytes.Slice.Chain (sgOf aO) :=
  (chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => rO s.st) restO aO lO).get (by
    obtain ⟨c, hc, _⟩ := chain_O
    rw [hc]
    rfl)

theorem cO_eq :
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => rO s.st) restO aO lO = some cO :=
  (Option.some_get _).symm

theorem cO_rds : cO.rds = lO.map WR.rd := by
  obtain ⟨c, hc, hr⟩ := chain_O
  obtain rfl := Option.some.inj (hc.symm.trans cO_eq)
  exact hr

/-- "BAT" draws one element and nothing else; its logN. -/
theorem ds_O : Fmt.dsOf w0O.entry w0O.kind = [.elem, .trits 0] := by decide +kernel
theorem log_O : w0O.entry.logN ≤ 64 := by decide +kernel

/-- The public half of what the payer asks, at 768. -/
theorem payPub_O : H2K.Pub.PayPub piO (fun s => rO s.st) w0O.entry.rows 768 := by
  have h := H2K.Pub.payPub_of_joh piO rO (fun s => rO s.st) (fun _ => rfl)
    member_O.2.2.2.2.2.2.1 w0O lO written_O
  rwa [o_v0] at h

end H2K.Member

#print axioms H2K.Member.written_O
#print axioms H2K.Member.cO_rds
#print axioms H2K.Member.payPub_O
#print axioms H2K.Member.depth_O
#print axioms H2K.Member.chain_O
