-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrameAt.lean: AT EVERY CUT OF A LINK l < 24 FROM BEHIND ITS FIRST
SUB-PROTOCOL TO IN FRONT OF ITS CLOSING: THE OPEN LINK's FRAME, WRITTEN OUT, AND THE LINK's GROUP's
MEMBERS AS THE FRAME's TWO LISTS: at the proof file's seat, in the goals' scope, from the fold's
return alone.
  At l pre fl f t: at t a link is open with the number l and the frame f; the statement's group
    number l has the members pre ++ f.keptBefore ++ f.own and the flags fl; a flag a member; no
    number twice. Below l t: every member of that group is below the number of messages.
  at_quiet, below_quiet; at_commit: kind K1's later sending grows the frame's list "own" and the
    group's members by the same numbers, raises the moment by 1, and lays the moment's flags behind
    the flags (K1.commitAtS_frame and K1.laterArrays_commitAtS, below Johnson/Desc/K1/Law/).
  Fr: GS on the statement and the open link's frame whole; rest_front: the batching, the
    sub-protocol behind it and the one equation keep what a Quiet step, the batching's maker and the
    one equation's keep (Johnson/IMR/LinkRest.lean's rest_by without the closing and the shutting).
  laterF f n: the frame behind a later sending, n the number of messages in front of it.
  hear_commitQ, hear_flat, step_quiet, step_commit: over one hearing sub-protocol.
  walk_a, walk_b, walk_c: THE TOPS: from At and Below at the cut 14 l + 3, with the frame f there:
    At at every cut 14 l + 3 + n, n ≤ 9, in three stretches: n ≤ 2: the frame f; n = 3, 4:
    laterF f n₃; 5 ≤ n ≤ 9: laterF (laterF f n₃) n₅; n₃, n₅ the numbers of messages in front of the
    two later sendings.
The entries (At and Below at the cut 14 l + 3, with f's fields): Johnson/IMR/FrameEntry.lean.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: the list of facts along the fold
(field "frameIs"); kind K8's, K10's and K2's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.GroupZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9
open ProofFile (Cl)

/-- The open link's frame, and its group's members as the frame's two lists. -/
structure At (l : Nat) (pre : Array Nat) (fl : List Bool) (f : ReqFrame) (t : S) : Prop where
  link : ∃ L, t.link? = some L ∧ L.check.frame = f ∧ L.link = l
  group : ∃ G, t.st.groups[l]? = some G ∧ G.members = pre ++ f.keptBefore ++ f.own ∧
    G.kept = fl.toArray ∧ G.kept.size = G.members.size ∧ G.members.toList.Nodup

/-- Every member of group number l is below the number of messages. -/
def Below (l : Nat) (t : S) : Prop :=
  ∀ G, t.st.groups[l]? = some G → ∀ o ∈ G.members, o < t.st.oracles.size

theorem at_quiet {l : Nat} {pre : Array Nat} {fl : List Bool} {f : ReqFrame} {s t : S}
    (q : Quiet s t) (H : At l pre fl f s) : At l pre fl f t := by
  obtain ⟨L, hL, e1, e2⟩ := H.link
  obtain ⟨L', a, c, -, n⟩ := quiet_fwd q hL
  exact ⟨⟨L', a, by rw [c]; exact e1, n.trans e2⟩, by rw [q.1.1]; exact H.group⟩

theorem below_quiet {l : Nat} {s t : S} (q : Quiet s t) (H : Below l s) : Below l t := by
  unfold Below
  rw [q.1.1]
  exact H

/-- The frame behind a later sending, n the number of messages in front of it: the moment is raised
by 1; the moment's messages' new numbers are laid behind "own". -/
def laterF (f : ReqFrame) (n : Nat) : ReqFrame :=
  { f with moment := f.moment + 1
           own := f.own ++ (Array.range (f.atMoment f.moment).length).map (· + n) }

/-- **Kind K1's later sending.** -/
theorem at_commit {Q : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s v : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs gs = .ok v)
    {l : Nat} {pre : Array Nat} {fl : List Bool} {f : ReqFrame} (hg : f.group = l)
    (H : At l pre fl f s) (B : Below l s) :
    At l pre (fl ++ K1.flagsAt f) (laterF f s.st.oracles.size) v ∧ Below l v := by
  obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two h
  obtain ⟨L, hL, e1, e2⟩ := H.link
  obtain ⟨G, hG, em, ek, es, hn⟩ := H.group
  obtain ⟨L₀, L', a1, a2, e, -⟩ := K1.commitAtS_frame Q link moment arrays s v r₁ r₂ gs h
  obtain rfl : L₀ = L := Option.some.inj (a1.symm.trans hL)
  obtain ⟨M, M', b1, b2, -, m2, -⟩ := K1.commitAtS_moments Q link moment arrays s v _ gs h
  obtain rfl : M = L₀ := Option.some.inj (b1.symm.trans hL)
  obtain rfl : M' = L' := Option.some.inj (b2.symm.trans a2)
  obtain ⟨Lk, hLk, hA⟩ := K1.laterArrays_commitAtS Q link moment arrays s v _ gs rfl h
  obtain rfl : Lk = M := Option.some.inj (hLk.symm.trans hL)
  have hgl : Lk.check.frame.group = l := by rw [e1]; exact hg
  rw [hgl] at hA
  obtain ⟨G', hG', gr⟩ := hA G hG (B G hG)
  have hsz := (K1.commitAtS_seated Q link moment arrays s v r₁ r₂ gs h).msgs
  have hlen := commit_len h hL
  rw [e1] at hlen e gr
  have hk : Q.sent.size = (f.atMoment f.moment).length := by
    simpa [K1.idsOf, K1.flagsAt] using hlen
  have hid : K1.idsOf Q s.st.oracles.size =
      (Array.range (f.atMoment f.moment).length).map (· + s.st.oracles.size) := by
    unfold K1.idsOf
    rw [hk]
  have em' : G'.members = pre ++ f.keptBefore ++ (laterF f s.st.oracles.size).own := by
    show _ = pre ++ f.keptBefore ++ (f.own ++ _)
    rw [gr.1, em, ← hid, Array.append_assoc (ys := f.own)]
  have ek' : G'.kept = (fl ++ K1.flagsAt f).toArray := by
    rw [gr.2 es, ek]
    simp
  refine ⟨⟨⟨M', a2, by rw [e, hid]; rfl, m2.trans e2⟩, G', hG', em', ek', ?_,
    gr.nodup_ids hn (B G hG)⟩, ?_⟩
  · have h1 : fl.length = G.members.size := by
      rw [← es, ek]
      simp
    have hlen' : (K1.idsOf Q s.st.oracles.size).size = (K1.flagsAt f).length := by
      simpa using hlen
    have s1 : G'.kept.size = fl.length + (K1.flagsAt f).length := by
      rw [ek']
      simp
    have s2 : G'.members.size = G.members.size + (K1.idsOf Q s.st.oracles.size).size := by
      rw [gr.1]
      simp
    rw [s1, s2, h1, hlen']
  · intro G₂ hG₂ o ho
    obtain rfl : G' = G₂ := Option.some.inj (hG'.symm.trans hG₂)
    rw [gr.1] at ho
    rcases Array.mem_append.1 ho with ho | ho
    · have := B G hG o ho
      omega
    · have ho' : o ∈ (K1.idsOf Q s.st.oracles.size).toList := by simpa using ho
      rw [K1.ids_list] at ho'
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ho'
      have := List.mem_range.1 hi
      omega

/-- GS on the statement, and the open link's frame whole. -/
def Fr (s t : S) : Prop := Calm s t ∧ GBy (fun f : ReqFrame => f) s t

theorem fr_refl (s : S) : Fr s s := ⟨calm_refl s, gby_refl _ s⟩

theorem fr_trans (a b c : S) (h : Fr a b) (k : Fr b c) : Fr a c :=
  ⟨calm_trans _ _ _ h.1 k.1, gby_trans _ _ _ _ h.2 k.2⟩

theorem fr_of_quiet {s t : S} (q : Quiet s t) : Fr s t := ⟨calm_of_quiet q, gby_of_quiet _ q⟩

theorem at_fr {l : Nat} {pre : Array Nat} {fl : List Bool} {f : ReqFrame} {s t : S}
    (q : Fr s t) (H : At l pre fl f s) : At l pre fl f t := by
  obtain ⟨L, hL, e1, e2⟩ := H.link
  obtain ⟨G, hG, em, ek, es, hn⟩ := H.group
  obtain ⟨L', a, c, n⟩ := q.2 L hL
  have pr := q.1.2 l
  rw [hG] at pr
  obtain ⟨G', hG', eG⟩ := Option.map_eq_some_iff.1 pr
  have m1 : G'.members = G.members := congrArg Prod.fst eG
  have m2 : G'.kept = G.kept := congrArg Prod.snd eG
  exact ⟨⟨L', a, c.trans e1, n.trans e2⟩, G', hG', by rw [m1, em], by rw [m2, ek],
    by rw [m1, m2, es], by rw [m1]; exact hn⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Numbers 14 l + 9 + n, n ≤ 2, of the flat list: the batching, the sub-protocol behind it, the one
equation. -/
theorem rest_front {R : S → S → Prop} (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    (hQ : ∀ s t, Quiet s t → R s t)
    (hBat : ∀ (p : K9.Where) {claims : S → Except String (List Claim × S)}, FnCl R claims →
      Decides R (K9.batch K9.atS p claims))
    (hEq : ∀ p : K9.Where, Decides R (K9.oneEquation (Cl := Unit) K9.atS p))
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {Lk : Link S Cl} (eL : c.links[l]? = some Lk)
    (hy : ∀ b₀, Lk.hear[0]? = some b₀ → ∃ s rs gs t, b₀.decide s rs gs = .ok t)
    {n : Nat} (hn : n ≤ 2) {b : Block S Cl} (hb : c.blocksInOrder[14 * l + 9 + n]? = some b) :
    Decides R b := by
  have hruns := hear_runs hr ht hQ hS hR O hl eL hy
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk', f, bL, bB, bC, eL', hlen, -, -, -, -, -, -, -, -, iB, -, dB, -⟩ := hfr l (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  · obtain ⟨Lk', p, w, T, eL', -, -, -, -, -, hal, ifl, -⟩ := (IM.k9_of hS hR O).2 l (by omega)
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    rw [hlen] at ifl
    obtain rfl := Option.some.inj (ifl.symm.trans hb)
    intro s rs gs t h
    exact hBat p (link_claims_runs hr ht Lk hruns) s rs gs t
      ((IM.yes_alone (hal _) (by unfold IM.a9Of; intro k; cases k) s t rs gs).1 h).1
  · rw [hlen] at iB
    obtain rfl := Option.some.inj (iB.symm.trans hb)
    intro s rs gs t h
    rw [dB] at h
    exact link_behind_runs hr ht Lk hruns s t h
  · obtain ⟨Lk', p, Q, eL', -, -, hall⟩ := IM.close_of hS hR O l (by omega)
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
    obtain ⟨b', x, e1, e2, la⟩ := hall 0 .K9 rfl
    have ib := IM.close_numbers hS hR O (by omega : l < 25) eL e1
    rw [hlen, show 14 * l + 7 + 4 + 0 = 14 * l + 9 + 2 by omega] at ib
    obtain rfl := Option.some.inj (ib.symm.trans hb)
    intro s rs gs t h
    have dx : x.retype.decide s rs gs = .ok t :=
      ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1
    obtain rfl : ({ K9.oneEquation K9.atS p with planOk := K9.fits p Q } : Block S Unit) = x :=
      Option.some.inj e2
    exact hEq p s rs gs t dx

/-- Hearing sub-protocols number 3 and 5 of a link l < 24: kind K1's later sending, then a Quiet
step. -/
theorem hear_commitQ (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {j : Nat} (hj : j = 3 ∨ j = 5) {Lk : Link S Cl} {b : Block S Cl}
    (eL : c.links[l]? = some Lk) (e : Lk.hear[j]? = some b) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : b.decide s rs gs = .ok t) :
    ∃ (Q : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) (v : S) (rs' : List Fmt.RoundView)
      (gs' : List (List (Nat × List UInt64))),
      (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs' gs' = .ok v ∧
        Quiet v t := by
  have hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[j]? = some KindName.K1 := by
    unfold IM.subAt
    rw [if_neg (by omega : ¬ l = 24)]
    rcases hj with rfl | rfl <;> split <;> cases (l == 0) <;> rfl
  obtain ⟨Lk', b', Xl, pr, pd, reads, digits, eL', e', -, -, harm⟩ :=
    IM.k1_later O l (IM.subAt l) (IM.subs_scope hS hR O l (by omega)) j hk
      (by rcases hj with rfl | rfl <;> decide)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain rfl : b = b' := Option.some.inj (e.symm.trans e')
  rcases harm with ⟨-, la⟩ | ⟨-, la⟩
  · have h' : (IM.k1Reads Z Bs.G₀ l Xl pr reads).decide s rs gs = .ok t :=
      ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1
    obtain ⟨v, a1, a2⟩ := andThen_yes h'
    exact ⟨_, _, _, _, v, _, _, a1, (orLoud_whole fun b hb => readsQuietAt_quiet hb).1 v _ _ t a2⟩
  · exact ⟨_, _, _, _, t, rs, gs, ((IM.yes_alone la (by intro k; cases k) s t rs gs).1 h).1,
      quiet_refl t⟩

/-- The hearing sub-protocols of link l < 24, by number in the flat list. -/
theorem hear_flat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24) :
    ∃ Lk, c.links[l]? = some Lk ∧
      ∀ j < 7, ∃ b, Lk.hear[j]? = some b ∧ c.blocksInOrder[14 * l + 2 + j]? = some b := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  refine ⟨Lk, eL, fun j hj => ?_⟩
  obtain ⟨b, e⟩ : ∃ b, Lk.hear[j]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by omega : j < Lk.hear.length)⟩
  refine ⟨b, e, ?_⟩
  have q := IM.hear_at_flat eL e
  rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) j).trans
    (by omega : 14 * l + j + 2 = 14 * l + 2 + j)] at q

/-- Over a Quiet hearing sub-protocol. -/
theorem step_quiet (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {j : Nat}
    (hj : j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 6) {s s' : S} {r r' : List Fmt.RoundView}
    {q q' : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q))
    (g' : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q')) :
    Quiet s s' := by
  obtain ⟨Lk, eL, hA⟩ := hear_flat hS hR O h24
  obtain ⟨b, e, ib⟩ := hA j (by omega)
  obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
  exact hear_quiet hS hR O h24 hj eL e s rs' gs' s' d'

/-- Over a later sending's sub-protocol. -/
theorem step_commit (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {j : Nat}
    (hj : j = 3 ∨ j = 5) {s s' : S} {r r' : List Fmt.RoundView}
    {q q' : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j)) (ProofFile.startS Z p) R C = .ok (s, r, q))
    (g' : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + j + 1)) (ProofFile.startS Z p) R C = .ok (s', r', q'))
    {pre : Array Nat} {fl : List Bool} {f : ReqFrame} (hg : f.group = l)
    (H : At l pre fl f s) (B : Below l s) :
    At l pre (fl ++ K1.flagsAt f) (laterF f s.st.oracles.size) s' ∧ Below l s' := by
  obtain ⟨Lk, eL, hA⟩ := hear_flat hS hR O h24
  obtain ⟨b, e, ib⟩ := hA j (by omega)
  obtain ⟨rs', gs', d'⟩ := fold_next ib g g'
  obtain ⟨Q, lk, mo, ar, v, rs2, gs2, cm, qv⟩ := hear_commitQ hS hR O h24 hj eL e d'
  obtain ⟨a1, a2⟩ := at_commit cm hg H B
  exact ⟨at_quiet qv a1, below_quiet qv a2⟩

/-- **THE FIRST STRETCH: the cuts 14 l + 3 + n, n ≤ 2.** -/
theorem walk_a (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    {pre : Array Nat} {fl : List Bool} {f : ReqFrame} (H1 : At l pre fl f t₁) (B1 : Below l t₁) :
    ∀ n ≤ 2, ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      At l pre fl f t ∧ Below l t
  | 0, _, t, r, q, g => by
    obtain rfl : t₁ = t := congrArg Prod.fst (Except.ok.inj (f₁.symm.trans g))
    exact ⟨H1, B1⟩
  | n + 1, hn, t, r, q, g => by
    obtain ⟨u, ru, qu, gu⟩ := fold_back (k := 14 * l + 3 + n) g
    obtain ⟨a1, a2⟩ := walk_a hS hR O h24 f₁ H1 B1 n (by omega) u ru qu gu
    have k := step_quiet hS hR O h24 (j := n + 1) (by omega)
      (by rw [show 14 * l + 2 + (n + 1) = 14 * l + 3 + n by omega]; exact gu)
      (by rw [show 14 * l + 2 + (n + 1) + 1 = 14 * l + 3 + (n + 1) by omega]; exact g)
    exact ⟨at_quiet k a1, below_quiet k a2⟩

/-- **THE SECOND STRETCH: the cuts 14 l + 6 and 14 l + 7.** t₃: the state in front of the first
later sending. -/
theorem walk_b (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₁ R₃ : List Fmt.RoundView} {C C₁ C₃ : List VerifiableInference.Desc.OpenedColumn}
    {t₁ t₃ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 5)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃))
    {pre : Array Nat} {fl : List Bool} {f : ReqFrame} (hg : f.group = l)
    (H1 : At l pre fl f t₁) (B1 : Below l t₁) :
    ∀ n ≤ 1, ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 6 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      At l pre (fl ++ K1.flagsAt f) (laterF f t₃.st.oracles.size) t ∧ Below l t := by
  have z : ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 6)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      At l pre (fl ++ K1.flagsAt f) (laterF f t₃.st.oracles.size) t ∧ Below l t := by
    intro t r q g
    obtain ⟨a1, a2⟩ := walk_a hS hR O h24 f₁ H1 B1 2 (by omega) t₃ R₃ C₃ f₃
    exact step_commit hS hR O h24 (j := 3) (Or.inl rfl) f₃ g hg a1 a2
  intro n hn t r q g
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · exact z t r q g
  · obtain ⟨u, ru, qu, gu⟩ := fold_back (k := 14 * l + 6) g
    obtain ⟨a1, a2⟩ := z u ru qu gu
    have k := step_quiet hS hR O h24 (j := 4) (by omega) gu g
    exact ⟨at_quiet k a1, below_quiet k a2⟩

/-- **THE THIRD STRETCH: the cuts 14 l + 8 + n, n ≤ 4: to in front of the closing.** t₅: the state
in front of the second later sending. -/
theorem walk_c (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₁ R₃ R₅ : List Fmt.RoundView}
    {C C₁ C₃ C₅ : List VerifiableInference.Desc.OpenedColumn} {t₁ t₃ t₅ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 5)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃))
    (f₅ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 7)) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅))
    {pre : Array Nat} {fl : List Bool} {f : ReqFrame} (hg : f.group = l)
    (H1 : At l pre fl f t₁) (B1 : Below l t₁) :
    ∀ n ≤ 4, ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      At l pre (fl ++ K1.flagsAt f ++ K1.flagsAt (laterF f t₃.st.oracles.size))
        (laterF (laterF f t₃.st.oracles.size) t₅.st.oracles.size) t
  | 0, _, t, r, q, g => by
    obtain ⟨a1, a2⟩ := walk_b hS hR O h24 f₁ f₃ hg H1 B1 1 (by omega) t₅ R₅ C₅ f₅
    exact (step_commit hS hR O h24 (j := 5) (Or.inr rfl) f₅ g (f := laterF f _) hg a1 a2).1
  | 1, _, t, r, q, g => by
    obtain ⟨u, ru, qu, gu⟩ := fold_back (k := 14 * l + 8) g
    exact at_quiet (step_quiet hS hR O h24 (j := 6) (by omega) gu g)
      (walk_c hS hR O h24 f₁ f₃ f₅ hg H1 B1 0 (by omega) u ru qu gu)
  | n + 2, hn, t, r, q, g => by
    obtain ⟨u, ru, qu, gu⟩ := fold_back (k := 14 * l + 8 + (n + 1)) g
    have a := walk_c hS hR O h24 f₁ f₃ f₅ hg H1 B1 (n + 1) (by omega) u ru qu gu
    obtain ⟨Lk, eL, hA⟩ := hear_flat hS hR O h24
    have hy : ∀ b₀, Lk.hear[0]? = some b₀ → ∃ s rs gs t, b₀.decide s rs gs = .ok t := by
      intro b₀ e0
      obtain ⟨b₀', e0', i0⟩ := hA 0 (by omega)
      obtain rfl : b₀ = b₀' := Option.some.inj (e0.symm.trans e0')
      obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
      obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
      exact ⟨_, _, _, _, d0⟩
    obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
    obtain ⟨Lk', -, -, -, bC, eL', hlen, -, -, -, -, -, -, -, -, -, -, -, iC, -⟩ := hfr l (by omega)
    rw [if_neg (by omega : ¬ l = 24)] at hlen
    rw [hlen] at iC
    obtain ⟨b, ib⟩ : ∃ b, c.blocksInOrder[14 * l + 9 + n]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by
        have := (List.getElem?_eq_some_iff.1 iC).1
        omega)⟩
    obtain ⟨rs, gs, d⟩ := fold_next ib
      (by rw [show 14 * l + 9 + n = 14 * l + 8 + (n + 1) by omega]; exact gu)
      (by rw [show 14 * l + 9 + n + 1 = 14 * l + 8 + (n + 2) by omega]; exact g)
    exact at_fr (rest_front fr_refl fr_trans (fun _ _ => fr_of_quiet)
      (fun p _ hcl s rs gs t h => ⟨(batch_calm p fun a y k => (hcl a y k).1).1 s rs gs t h,
        batch_gby _ p (fun a y k => (hcl a y k).2) s rs gs t h⟩)
      (fun p s rs gs t h => ⟨oneEquation_calm (Cl := Unit) p s rs gs t h,
        oneEquation_gby _ (C := Unit) p s rs gs t h⟩)
      hS hR O h24 eL hy (by omega) ib u rs gs t d) a

end

#print axioms at_commit
#print axioms rest_front
#print axioms walk_a
#print axioms walk_b
#print axioms walk_c

end Meaning.K2
