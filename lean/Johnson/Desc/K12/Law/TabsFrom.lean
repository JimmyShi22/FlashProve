-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.TabOnto
import Johnson.Desc.K12.Law.AccKYes
/-
Johnson/Desc/K12/Law/TabsFrom.lean: (T2) TABLES FOR THE LATER STAGES' TREES: BY RECURSION ON THE CHAIN, BESIDE Dealt AND TiedW: dealt groups that fit the declared openings follow the written columns of SOME blocks' transcripts. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
THE RECURSION, AND THE FRAGMENTS hdS · hnext (which written round is the switch's first; the next stage's rounds) ARE wideFrom | wideFirst (Johnson/Desc/K12/Law/ViewWide.lean), READ BACKWARDS: there: every written column has the wanted width; here: columns of the wanted form are written columns of some oracle.
  GOk o grp · GFit ops gs   a dealt group fits a declared opening: its positions differ, each is below 2 ^ a, each column has W words · group by group
  table_of_gok   a table for the tree of one opening (table_onto, Johnson/Desc/K12/Law/TabOnto.lean)
  dOrcs          the default oracles of a list of rounds
  opens_nil      a cut that opens nothing and stores nothing has no declared opening
  tabsFrom       from a stage j ≠ 0 on: GFit of all declared openings from that stage on ⇒ ∃ o (the stage's own tree's oracle) and b, Follows gs (srcFrom c d o b l)
  tabsFirst      the whole test behind "BAT": GFit · the first switch's groups follow gT at the places ts ⇒ for every first message m1: ∃ b whose first message has m1's oracle, Follows gs (srcFirst c b l ts gT)
WHAT IS LEFT FOR «tables_of_view»: (T3): W0 | fM | m1 at the first stage, so that the first switch's groups follow them, with DeepK · GFit from Block.step's second test at a real view.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.Pub (WR writtenOf kk sgOf chainFrom Letters)
open H2K.Onto (Orcs orcsOf tr_with)

/-- A dealt group fits a declared opening. -/
def GOk (o : Fmt.Shape × Fmt.TreeSource) (grp : List (ℕ × List UInt64)) : Prop :=
  (grp.map (·.1)).Nodup ∧ ∀ x ∈ grp, x.1 < 2 ^ o.1.a ∧ x.2.length = o.1.W

abbrev GFit (ops : List (Fmt.Shape × Fmt.TreeSource)) (gs : Gs) : Prop := List.Forall₂ GOk ops gs

theorem table_of_gok (d : PQ.RD) (o0 : Fmt.Shape × Fmt.TreeSource) (hd : d.tree = some o0.1)
    (grp : List (ℕ × List UInt64)) (h : GOk o0 grp) :
    ∃ o : (wRound d).Orc, ∀ x ∈ grp, x.2 = colW d o x.1 :=
  table_onto d grp
    (fun x hx y hy e => congrArg Prod.snd (List.inj_on_of_nodup_map h.1 hx hy e))
    (fun x hx => by rw [hd]; exact (h.2 x hx).1) (fun x hx => by rw [hd]; exact (h.2 x hx).2)

def dOrcs : (ds : List PQ.RD) → Orcs ds
  | [] => ()
  | d :: ds => ((wRound d).dOrc, dOrcs ds)

theorem opens_nil : ∀ (cut : List Fmt.DeclaredRound), nOpen cut = 0 → cut.flatMap (·.opens) = []
  | [], _ => rfl
  | d :: l, h => by
    rw [nOpen_cons] at h
    rw [List.flatMap_cons, opens_nil l (by omega), List.append_nil]
    exact List.eq_nil_of_length_eq_zero (by omega)

theorem opens_split (l : Laid) (k : ℕ) (h0 : nOpen (cutF l k) = 0) :
    (l.map (·.1)).flatMap (·.opens) =
      (cutS l k).flatMap (·.opens) ++ ((l.drop (k + 3)).map (·.1)).flatMap (·.opens) := by
  conv_lhs => rw [← List.take_append_drop (k + 3) (l.map (·.1)), List.flatMap_append, take_cut,
    List.flatMap_append, opens_nil _ h0, List.nil_append]
  rw [List.map_drop]

theorem forall₂_split {α β : Type} (R : α → β → Prop) : ∀ (a b : List α) (l : List β),
    List.Forall₂ R (a ++ b) l →
    ∃ l1 l2, List.Forall₂ R a l1 ∧ List.Forall₂ R b l2 ∧ l = l1 ++ l2
  | [], _, l, h => ⟨[], l, List.Forall₂.nil, h, rfl⟩
  | _ :: a, b, _, h => by
    cases h with
    | cons h1 h2 =>
      obtain ⟨l1, l2, a1, a2, rfl⟩ := forall₂_split R a b _ h2
      exact ⟨_ :: l1, l2, List.Forall₂.cons h1 a1, a2, rfl⟩

theorem head_orc (d : PQ.RD) (ds : List PQ.RD) (τ : Tr (PQ.uL (ckP .two) (d :: ds)))
    (o : (wRound d).Orc) (os : Orcs ds) (h : orcsOf (d :: ds) τ = (o, os)) : τ.1.1 = o := by
  obtain ⟨m, _, _⟩ := τ
  exact (Prod.mk.inj h).1


theorem tabsFrom (p : P12) : ∀ {s : Sg} (c : OnBytes.Slice.Chain s) (j : ℕ) (cur : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (l : Laid) (w : List WR), stagesOf c = cur :: rest →
    c.rds = w.map WR.rd → j ≠ 0 → Dealt p j cur rest l → TiedW j cur rest l w →
    ∀ (d : PQ.RD) (o0 : Fmt.Shape × Fmt.TreeSource), (cutN cur rest l).flatMap (·.opens) = [o0] →
    d.tree = some o0.1 → ∀ (gs : Gs), GFit ((l.map (·.1)).flatMap (·.opens)) gs →
    ∃ (o : (wRound d).Orc) (b : c.Bl), Follows gs (srcFrom c d o b l) := by
  intro s c
  induction c with
  | last s e dL dB fu fs εb =>
    intro j cur rest l w hs _ _ _ _ d o0 h1 hd gs hg
    obtain ⟨_, rfl⟩ := List.cons.inj (show [s.st] = cur :: rest from hs)
    have h1' : (l.map (·.1)).flatMap (·.opens) = [o0] := h1
    rw [h1'] at hg
    cases hg with
    | cons hg0 hg' =>
      cases hg'
      rename_i g0
      obtain ⟨o, ho⟩ := table_of_gok d o0 hd g0 hg0
      obtain ⟨τ, _⟩ := tr_with [dL, dB] (dOrcs _)
      refine ⟨o, τ, fun i grp hi x hx => ?_⟩
      show x.2 = colW d o x.1
      cases i with
      | zero =>
        obtain rfl : g0 = grp := Option.some.inj hi
        exact ho x hx
      | succ i => cases hi
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro j cur rest l w hs hr hj hD hT d o0 h1 hd gs hg
    obtain ⟨rfl, hrest⟩ := List.cons.inj (show s.st :: stagesOf next = cur :: rest from hs)
    cases hn : stagesOf next with
    | nil =>
      exfalso
      cases next <;> cases hn
    | cons nxt rest' =>
      rw [hn] at hrest
      subst hrest
      obtain ⟨d1, d2, d3⟩ := hD
      obtain ⟨⟨dSw, o1, t1, t2, t3⟩, t4⟩ := hT
      obtain ⟨oc, hoc⟩ := d2 hj
      have hk : s.st.k = s.h + s.g := rfl
      rw [kk_st] at t1 t4
      rw [hk] at d1 d3 t2 t4 hoc
      have hcut : cutN s.st (nxt :: rest') l = cutS l (s.h + s.g) := rfl
      rw [hcut] at h1
      have hnS : nOpen (cutS l (s.h + s.g)) = 1 := hoc.nOpen
      have hdS : dS = dSw.rd := by
        have hfl : (foldRds s dE dT).length = 1 + (s.h + s.g) := by
          simp [foldRds]
          omega
        have h3 : (foldRds s dE dT ++ ([dS, dC] ++ next.rds))[1 + (s.h + s.g)]? = some dS := by
          rw [List.getElem?_append_right (by rw [hfl]), hfl, Nat.sub_self]
          rfl
        have hr' : foldRds s dE dT ++ ([dS, dC] ++ next.rds) = w.map WR.rd := hr
        rw [hr', List.getElem?_map, t1] at h3
        exact (Option.some.inj h3).symm
      have hnext : next.rds = (w.drop (s.h + s.g + 3)).map WR.rd := by
        have hr' : foldRds s dE dT ++ ([dS, dC] ++ next.rds) = w.map WR.rd := hr
        rw [List.map_drop, ← hr']
        have hl : (foldRds s dE dT ++ [dS, dC]).length = s.h + s.g + 3 := by simp [foldRds]
        rw [← List.append_assoc, ← hl, List.drop_left]
      rw [opens_split l (s.h + s.g) d1, h1] at hg
      cases hg with
      | cons hg0 hg' =>
        rename_i g0 gs'
        obtain ⟨o, ho⟩ := table_of_gok d o0 hd g0 hg0
        obtain ⟨o', b', hb'⟩ := ih (j + 1) nxt rest' (l.drop (s.h + s.g + 3))
          (w.drop (s.h + s.g + 3)) hn hnext (Nat.succ_ne_zero j) d3 t4 dS o1 t2
          (by rw [hdS]; exact t3) gs' hg'
        obtain ⟨τF, _⟩ := tr_with (foldRds s dE dT) (dOrcs _)
        obtain ⟨τS, hS⟩ := tr_with [dS, dC] (o', dOrcs [dC])
        have hS1 : τS.1.1 = o' := head_orc dS [dC] τS o' _ hS
        refine ⟨o, (τF, τS, b'), fun i grp hi x hx => ?_⟩
        show x.2 = (if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then
            colW d o x.1
          else srcFrom next dS τS.1.1 b' (l.drop (s.h + s.g + 3))
            (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) x.1)
        rw [d1, hnS, hS1]
        cases i with
        | zero =>
          obtain rfl : g0 = grp := Option.some.inj hi
          rw [if_pos (by omega)]
          exact ho x hx
        | succ i =>
          rw [if_neg (by omega), show i + 1 - (0 + 1) = i by omega]
          exact hb' i grp hi x hx


theorem tabsFirst (p : P12) {s : Sg} (c : OnBytes.Slice.Chain s) (cur : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (l : Laid) (w : List WR) (hs : stagesOf c = cur :: rest)
    (hr : c.rds = w.map WR.rd) (hD : Dealt p 0 cur rest l) (hT : TiedW 0 cur rest l w)
    (ts : List ℕ) (gT : ℕ → ℕ → List UInt64) (gs : Gs)
    (hg : GFit ((l.map (·.1)).flatMap (·.opens)) gs)
    (hfirst : ∀ (i : ℕ) (grp : List (ℕ × List UInt64)), i < nOpen (cutS l cur.k) →
      gs[i]? = some grp → ∀ x ∈ grp, x.2 = gT (ts.getD i 0) x.1)
    (hnS : nOpen (cutS l cur.k) = ((cutS l cur.k).flatMap (·.opens)).length)
    (m1 : H2K.Pub.Msg1 c) :
    ∃ b : c.Bl, orc1 c (H2K.Pub.msg1 c b) = orc1 c m1 ∧ Follows gs (srcFirst c b l ts gT) := by
  cases c with
  | last s e dL dB fu fs εb =>
    obtain ⟨_, rfl⟩ := List.cons.inj (show [s.st] = cur :: rest from hs)
    exact absurd rfl hD.1
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    obtain ⟨rfl, hrest⟩ := List.cons.inj (show s.st :: stagesOf next = cur :: rest from hs)
    cases hn : stagesOf next with
    | nil =>
      exfalso
      cases next <;> cases hn
    | cons nxt rest' =>
      rw [hn] at hrest
      subst hrest
      obtain ⟨d1, _, d3⟩ := hD
      obtain ⟨⟨dSw, o1, t1, t2, t3⟩, t4⟩ := hT
      have hk : s.st.k = s.h + s.g := rfl
      rw [kk_st] at t1 t4
      rw [hk] at d1 d3 t2 t4 hfirst hnS
      have hfl : (foldRds s dE dT).length = 1 + (s.h + s.g) := by
        simp [foldRds]
        omega
      have hdS : dS = dSw.rd := by
        have h3 : (foldRds s dE dT ++ ([dS, dC] ++ next.rds))[1 + (s.h + s.g)]? = some dS := by
          rw [List.getElem?_append_right (by rw [hfl]), hfl, Nat.sub_self]
          rfl
        have hr' : foldRds s dE dT ++ ([dS, dC] ++ next.rds) = w.map WR.rd := hr
        rw [hr', List.getElem?_map, t1] at h3
        exact (Option.some.inj h3).symm
      have hnext : next.rds = (w.drop (s.h + s.g + 3)).map WR.rd := by
        have hr' : foldRds s dE dT ++ ([dS, dC] ++ next.rds) = w.map WR.rd := hr
        rw [List.map_drop, ← hr']
        have hl : (foldRds s dE dT ++ [dS, dC]).length = s.h + s.g + 3 := by simp [foldRds]
        rw [← List.append_assoc, ← hl, List.drop_left]
      rw [opens_split l (s.h + s.g) d1] at hg
      obtain ⟨g1, g2, hg1, hg2, rfl⟩ := forall₂_split _ _ _ _ hg
      have hl1 : g1.length = nOpen (cutS l (s.h + s.g)) := by rw [hnS, hg1.length_eq]
      obtain ⟨o', b', hb'⟩ := tabsFrom p next 1 nxt rest' (l.drop (s.h + s.g + 3))
        (w.drop (s.h + s.g + 3)) hn hnext (Nat.succ_ne_zero 0) d3 t4 dS o1 t2
        (by rw [hdS]; exact t3) g2 hg2
      obtain ⟨τF, hF⟩ := tr_with (foldRds s dE dT)
        ((show (wRound dE).Msg from m1).1, dOrcs (List.replicate (s.h + s.g) dT))
      obtain ⟨τS, hS⟩ := tr_with [dS, dC] (o', dOrcs [dC])
      have hS1 : τS.1.1 = o' := head_orc dS [dC] τS o' _ hS
      have hF1 : τF.1.1 = (show (wRound dE).Msg from m1).1 := head_orc dE _ τF _ _ hF
      refine ⟨(τF, τS, b'), congrArg (fun o => (⟨dE, o⟩ : WO)) hF1, fun i grp hi x hx => ?_⟩
      show x.2 = (if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then
          gT (ts.getD (i - nOpen (cutF l (s.h + s.g))) 0) x.1
        else srcFrom next dS τS.1.1 b' (l.drop (s.h + s.g + 3))
          (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) x.1)
      rw [d1, hS1, Nat.zero_add, Nat.sub_zero]
      by_cases hlt : i < nOpen (cutS l (s.h + s.g))
      · rw [if_pos hlt]
        exact hfirst i grp hlt hi x hx
      · rw [if_neg hlt]
        rw [List.getElem?_append_right (by omega), hl1] at hi
        exact hb' _ grp hi x hx

end H2K.First

#print axioms H2K.First.tabsFrom
#print axioms H2K.First.tabsFirst
