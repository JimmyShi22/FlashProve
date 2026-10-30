-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/TabsAtReach.lean: CONDITIONAL, under the library's one head on the public
input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): at every state that the first chain's own
sub-protocols reach at the border in front of the smallness test's draw of an attention segment
(number 14 (2 g + 1) + 6 of the flat list), the list of tables is closed and has the shapes that the
draw's place expects: `K8.tabs` (Johnson/Desc/First/K8/Hear.lean) at the numbers that the verifier's
own text gives that place (`ProofFile.k8Par`, Johnson/Desc/ProofFile/Lot/K8.lean).

Why. The draw's decision holds the closed list (of each table its matrix, the rows to an entry and
its first entry) against `K8.tabs` of its place. The library's law on that decision at an attention
segment (Johnson/Desc/First/K8/LawReadyAtt.lean) takes "the closed list has the place's shapes" as a
premise on the state in front of the draw.

How. `tabs_reads_k8Par` (Johnson/Desc/K5/Honest/Law/TabsAt.lean) has the shapes at the state just
behind a yes of the quiet step that makes and closes the list. That step is joined behind the
sending at number 14 (2 g + 1) + 5 (`ReadsMember`, Johnson/Desc/K5/Honest/Law/ReadsAtHead.lean:
which sub-protocol stands there, as a term). A state that is reached one number further on is the
result of that sub-protocol's yes; its dress (a test "no mark", a guard on the reply) hands on the
joined block's own result or refuses; the joined block's second half is the quiet step (`quiet_is`,
Johnson/Desc/K5/Honest/Law/ReadsAfter.lean).

Main names:
  `reach_last`: a state reached at a number k + 1 is the result of a yes of the sub-protocol number
    k at a state reached at k. General.
  `seated_reads_inv`: a yes of the sub-protocol as it stands in the chain holds a yes of the
    sending's own decision and, behind it, a yes of the quiet step with the same result.
  `tabs_at_reach`: **the list is closed and has the place's shapes.**
  `tabs_of_return`: on the honest side's road: the shapes of the tables of any return of `tablesP`
    at points made by `ptsFrom`, at the plan's numbers.

Limits. Shapes alone: nothing on the tables' weights. The head is a hypothesis. That the draw stands
at number 14 (2 g + 1) + 6, and that its place's numbers are `ProofFile.k8Par` at these letters, is not
shown here. Where no state is reached there the theorem says nothing. At the function
`OnBytes.secondHashFunction`, of which nothing is asked here; at the library's full size alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.ReadsAtHead
import Johnson.Desc.K5.Honest.Law.TabsAt
import Johnson.Desc.First.K8.LawReadyAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.K1 (laterAt)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open P5J (AtMgA TS)

/-- A state reached at a number k + 1 is the result of a yes of the sub-protocol number k at a state
reached at k. Conditional: h. -/
theorem reach_last {St Cl P : Type} {ft : ℕ} {bs : List (Block St Cl)} {start : P → St} {k : ℕ}
    {z : P} {s' : St} (h : Reach ft bs start (k + 1) (z, s')) :
    ∃ s b, Reach ft bs start k (z, s) ∧ bs[k]? = some b ∧ StepYes ft b s s' := by
  cases h with
  | succ h1 hb hy => exact ⟨_, _, h1, hb, hy⟩

/-- **A yes of the sub-protocol as it stands in the first chain holds a yes of the sending's own
decision, at its share of the rounds and the groups, and behind it a yes of the quiet step with the
same result.** Conditional: hk, hA: the link is of the attention sort and its group has the plan
A; hy: the yes. -/
theorem seated_reads_inv (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : Stages.LinkH)
    (reads : Option (List ℕ)) (name : String) {A : Attention.Plan} (hk : X.kind = 1)
    (hA : G.W.A[X.g]? = some A) {s s₂ : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (hy : (IM.seatedAs ProofFile.sameReply (IM.k1Reads Z G l X 4 reads).retype name
      ⟨1, some l, 4, .K1⟩).decide s rs gs = .ok s₂) :
    ∃ m, (laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1 reads).decide s
        (rs.take (laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1
          reads).rounds.length)
        (gs.take (laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1
          reads).openings) = .ok m ∧ readsAtSO A m = .ok s₂ := by
  have h5 : (((IM.k1Reads Z G l X 4 reads).decide s rs gs).bind fun t =>
      match t.failed with
      | none => .ok t
      | some e => .error ("marked: " ++ e)).bind
    (VerifiableInference.Desc.seatSame ProofFile.sameReply s) = .ok s₂ := hy
  cases hd : (IM.k1Reads Z G l X 4 reads).decide s rs gs with
  | error e =>
    rw [hd] at h5
    cases h5
  | ok t =>
    rw [hd] at h5
    have h6 : ((match t.failed with
        | none => (.ok t : Except String S)
        | some e => .error ("marked: " ++ e))).bind
      (VerifiableInference.Desc.seatSame ProofFile.sameReply s) = .ok s₂ := h5
    cases hf : t.failed with
    | some e =>
      rw [hf] at h6
      cases h6
    | none =>
      rw [hf] at h6
      have h7 : VerifiableInference.Desc.seatSame ProofFile.sameReply s t = .ok s₂ := h6
      have et : t = s₂ := by
        unfold VerifiableInference.Desc.seatSame at h7
        split at h7
        · exact Except.ok.inj h7
        · cases h7
      subst et
      unfold IM.k1Reads at hd
      have h8 : ((laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1
          reads).decide s (rs.take (laterAt (Cl := Unit) G.first
            (VerifiableInference.Desc.K1.gpOf Z) l 4 1 reads).rounds.length)
          (gs.take (laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1
            reads).openings)).bind (fun s' => (IM.k1Quiet G l X).decide s'
          (rs.drop (laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1
            reads).rounds.length)
          (gs.drop (laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1
            reads).openings)) = .ok t := hd
      cases h1 : (laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1
          reads).decide s (rs.take (laterAt (Cl := Unit) G.first
            (VerifiableInference.Desc.K1.gpOf Z) l 4 1 reads).rounds.length)
          (gs.take (laterAt (Cl := Unit) G.first (VerifiableInference.Desc.K1.gpOf Z) l 4 1
            reads).openings) with
      | error e =>
        rw [h1] at h8
        cases h8
      | ok m =>
        rw [h1] at h8
        refine ⟨m, rfl, ?_⟩
        rw [← quiet_is G l X hk hA m _ _]
        exact h8

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **AT EVERY STATE REACHED IN FRONT OF THE SMALLNESS TEST's DRAW OF AN ATTENTION SEGMENT THE LIST
OF TABLES IS CLOSED AND HAS THE PLACE's SHAPES.** G₀, Xl, pd, reads, digits, b: letters, under the
ties M (`member_at_head` hands a member; `ReadsMember.one`: the letters are fixed). Conditional: the
head; hg; M; hr: the state is reached at number 14 (2 g + 1) + 6. -/
theorem tabs_at_reach {g : ℕ} (hg : g < 12) {G₀ : ProofFile.Ground} {Xl : Stages.LinkH} {pd : ℕ}
    {reads digits : Option (List ℕ)} {b : Block S ProofFile.Cl}
    (M : ReadsMember Zp cF g G₀ Xl pd reads digits b) {π : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 6) (π, s)) :
    ∃ tl, s.tl? = some tl ∧ tl.funClosed = true ∧
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) =
        K8.tabs (ProofFile.k8Par Zp G₀ Xl (2 * g + 1)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans M.blank)
  obtain ⟨_, A, _, X, _, eA, _, _, _, _, _, _, eX, etl, _⟩ :=
    (IM.ground_tails h.scope h.reads O.pub O.blank).1 g hg
  obtain rfl : X = Xl := Option.some.inj (eX.symm.trans M.built)
  have hA : Bs.G₀.W.A[X.g]? = some A := by
    rw [M.group]
    exact eA
  obtain ⟨s0, b', _, hb, R, c, _, e⟩ :=
    reach_last (k := 14 * (2 * g + 1) + 5) hr
  obtain rfl : b = b' := Option.some.inj (M.flat.symm.trans hb)
  obtain ⟨_, _, _, h4⟩ := (step_ok_iff 0 b s0 s R c c.length).1 e
  rw [M.is] at h4
  obtain ⟨m, _, hm⟩ := seated_reads_inv Zp Bs.G₀ (2 * g + 1) X reads b.name M.kind hA h4
  obtain ⟨tl0, funs, _, e2, _⟩ := K8.Ready.attO_yes A m s hm
  exact ⟨_, e2, rfl, tabs_reads_k8Par Zp Bs.G₀ X (2 * g + 1) M.kind hA etl hm _ e2⟩

end

/-- **On the honest side's road**: the tables of any return of `tablesP` at the plan's numbers, at
points that `ptsFrom` makes, have the shapes of a place par. Conditional: ha, hk, hm: the place's
families, columns and rows are the plan's (`k8Par_attention` shows the three at the verifier's own
place); hp, ht: the two returns. `reads_at_border` (Johnson/Desc/K5/Honest/Law/ReadsAtHead.lean)
hands out the state behind the sending with just such a t laid. -/
theorem tabs_of_return (A : Attention.Plan) (par : K8.Par)
    (ha : par.asks = K8.Asks.attention A.S) (hk : par.ks = A.mats.toList.map (·.k))
    (hm : par.ms = A.mats.toList.map (·.m)) {zk : Array (Array E)} {hh : P.Heard} {F : Fork}
    {lk : P.LookIn} {p : P.Pts} {t : P.TablesP}
    (hp : P.ptsFrom (P.parCOf A).geo zk hh F = some p)
    (ht : P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW lk p = some t) :
    (tabsBack t).funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = K8.tabs par := by
  unfold P.ptsFrom at hp
  obtain ⟨Lf, _, hp'⟩ := Option.bind_eq_some_iff.1 hp
  rw [← tabs_attention_pts (mats := (P.parCOf A).mats) par ha
    (fun M => by rw [hk]; exact Tabs.getD_of_map (·.k) (·.2) rfl (fun _ => rfl) A.mats M)
    (fun M => by rw [hm]; exact Tabs.getD_of_map (·.m) (·.1) rfl (fun _ => rfl) A.mats M) hp' ht]
  show ((t.funs.map funBack).toList.map fun Fn : HFun => (Fn.mat, Fn.len, Fn.start)) = _
  rw [Array.toList_map, List.map_map]
  rfl

end H2K5.Honest

#print axioms H2K5.Honest.reach_last
#print axioms H2K5.Honest.seated_reads_inv
#print axioms H2K5.Honest.tabs_at_reach
#print axioms H2K5.Honest.tabs_of_return
