-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkShown.lean: THE RECORDS' ROAD: FROM «BY KEY» TO «BY GROUP»: what a view shows
under a tree's key (the library's Shows | Chain.ShowsFrom, OnBytes/Slice/BlkSeat.lean:50 ·
ManyShows.lean:41) as what
stands in the groups of columns that Block.step deals (ShownFrom | ShownLater,
Johnson/Desc/K12/Law/JointK.lean). General in the chain; nothing of the link is in it.
  ksOf ds            the numbers of the trees that declared rounds open, in turn: one a group, where
  no round reads a stored table and the chain's first tree has the number 0
  KeyedIn o ks gs    group by group: every column of the group stands in the list o under the
  group's key
  regroup_keyed · groupsOf_keys · keyedIn_of_step    Block.step's test «the columns» gives KeyedIn
  at the columns that it hands
  OpensAre c ds n    PUBLIC, on the plan alone, by recursion along the chain: a stage's fold opens
  nothing; its switch's two rounds open the tree number n alone; the next stage's the tree n + 1;
  the base case's
                     rounds the last
  shownFrom_of_keys  KeyedIn · OpensAre · Shows V n (the tree of the chain's first stage) ·
  ShowsFrom V (n + 1) ⟹ ShownFrom: its first clause: the first switch's columns are the written
  oracle's; its
                     second: ShownLater
No run of `verify-on-bytes`. Nothing on soundness by itself.
-/
import Johnson.Desc.Link.LinkReads
import Johnson.Desc.K12.Law.StepGroups
import OnBytes.Slice.ManyShows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open H2K.Sw H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem f2_trans {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop} {T : α → γ → Prop}
    (H : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l1 : List α} {l2 : List β} {l3 : List γ}, List.Forall₂ R l1 l2 → List.Forall₂ S l2 l3 →
        List.Forall₂ T l1 l3
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (H _ _ _ h1 h2) (f2_trans H t1 t2)

theorem f2_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ b ∈ l2, ∃ a ∈ l1, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h1 t1, b, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, h1⟩
    · obtain ⟨a, ha, hr⟩ := f2_mem_right t1 b h
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

def ksOf (ds : List Fmt.DeclaredRound) : List Nat := ds.flatMap fun r => r.opens.map (·.1.tree)

theorem ksOf_append (a b : List Fmt.DeclaredRound) : ksOf (a ++ b) = ksOf a ++ ksOf b :=
    List.flatMap_append

theorem nOpen_ks : ∀ (l : List Fmt.DeclaredRound), (∀ r ∈ l, r.stored = []) → nOpen l = (ksOf l).length
  | [], _ => rfl
  | d :: l, h => by
    rw [nOpen_cons, nOpen_ks l fun r hr => h r (List.mem_cons_of_mem _ hr), h d List.mem_cons_self]
    simp [ksOf]

def KeyedIn (o : List OpenedColumn) (ks : List Nat) (gs : Gs) : Prop :=
  List.Forall₂ (fun key grp => ∀ x ∈ grp, (key, x.1, x.2) ∈ o) ks gs

theorem regroup_keyed : ∀ (groups : List (List Want)) (got : List OpenedColumn), got.map kpw = groups.flatMap
    id →
    List.Forall₂ (fun want grp => ∀ x ∈ grp, ∃ w ∈ want, (w.1, x.1, x.2) ∈ got) groups
      (regroup (groups.map (·.length)) got)
  | [], _, _ => .nil
  | g :: gs, got, h => by
    rw [List.flatMap_cons] at h
    have h1 : (got.take g.length).map kpw = g := by
      rw [List.map_take, h]
      exact List.take_left' rfl
    have h2 : (got.drop g.length).map kpw = gs.flatMap id := by
      rw [List.map_drop, h]
      exact List.drop_left' rfl
    show List.Forall₂ _ (g :: gs) (((got.take g.length).map fun c => (c.2.1, c.2.2)) ::
      regroup (gs.map (·.length)) (got.drop g.length))
    refine .cons ?_ ((regroup_keyed gs _ h2).imp ?_)
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
      exact ⟨kpw c, by rw [← h1]; exact List.mem_map_of_mem hc, List.mem_of_mem_take hc⟩
    · intro want grp hh x hx
      obtain ⟨w, hw, hm⟩ := hh x hx
      exact ⟨w, hw, List.mem_of_mem_drop hm⟩

theorem groupsOf_keys : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn), (∀ d ∈ ds, d.stored = [])
    →
    ds.length = Rs.length →
    List.Forall₂ (fun key (want : List Want) => ∀ w ∈ want, w.1 = key) (ksOf ds) (groupsOf 0 ds Rs)
  | [], [], _, _ => .nil
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | d :: ds, R :: Rs, h, hl => by
    rw [groupsOf_cons]
    unfold grp1
    rw [h d List.mem_cons_self]
    show List.Forall₂ _ (d.opens.map (·.1.tree) ++ ksOf ds) _
    simp only [List.map_nil, List.nil_append]
    refine List.rel_append ?_ (groupsOf_keys ds Rs (fun x hx =>
      h x (List.mem_cons_of_mem _ hx)) (by simpa using hl))
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun o _ w hw => ?_
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hw
    exact Nat.sub_zero _

theorem keyedIn_of_step (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (got o : List OpenedColumn)
    (hst : ∀ d ∈ ds, d.stored = []) (hl : ds.length = Rs.length)
    (hc : got.map kpw = (groupsOf 0 ds Rs).flatMap id) (hsub : ∀ c ∈ got, c ∈ o) :
    KeyedIn o (ksOf ds) (regroup ((groupsOf 0 ds Rs).map (·.length)) got) :=
  f2_trans (fun key want grp h1 h2 x hx => by
    obtain ⟨w, hw, hm⟩ := h2 x hx
    rw [← h1 w hw]
    exact hsub _ hm) (groupsOf_keys ds Rs hst hl) (regroup_keyed _ _ hc)

def OpensAre : {s : Sg} → Chain s → List Fmt.DeclaredRound → Nat → Prop
  | _, .last _ _ _ _ _ _ _ => fun l n => ∀ key ∈ ksOf l, key = n
  | s, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ next => fun l n =>
    ksOf (l.take (1 + (s.h + s.g))) = [] ∧ (∀ key ∈ ksOf ((l.drop (1 + (s.h + s.g))).take 2), key =
        n) ∧
      OpensAre next (l.drop (s.h + s.g + 3)) (n + 1)

theorem shownFrom_of_keys (V : Fmt.View) : ∀ {s : Sg} (c : Chain s) (d : PQ.RD) (m : (wRound d).Msg)
    (n : ℕ)
    (b : c.Bl) (l : Laid) (gs : Gs), (∀ r ∈ l, r.1.stored = []) → KeyedIn V.opened
        (ksOf (l.map (·.1))) gs →
    OpensAre c (l.map (·.1)) n → Shows V n (treeCol d m) → c.ShowsFrom V (n + 1) b →
    ShownFrom c d m.1 b l gs := by
  intro s c
  induction c with
  | last s e dL dB fu fs εb =>
    intro d m n b l gs _ hK hO hS _
    show ∀ grp ∈ gs, ∀ x ∈ grp, x.2 = colW d m.1 x.1
    intro grp hg x hx
    obtain ⟨key, hk, hr⟩ := f2_mem_right hK grp hg
    have hkn : key = n := hO key hk
    exact treeCol_some d m x.1 x.2 (hS _ (hr x hx) hkn)
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro d m n b l gs hst hK hO hS hF
    obtain ⟨o1, o2, o3⟩ := hO
    obtain ⟨hF1, hF2⟩ := hF
    have hstD : ∀ r ∈ l.map (·.1), r.stored = [] := fun r hr => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hr
      exact hst y hy
    have eF : cutF l (s.h + s.g) = (l.map (·.1)).take (1 + (s.h + s.g)) := by
      unfold cutF
      rw [List.map_take]
    have eS : cutS l (s.h + s.g) = ((l.map (·.1)).drop (1 + (s.h + s.g))).take 2 := by
      unfold cutS
      rw [List.map_take, List.map_drop]
    have aF : nOpen (cutF l (s.h + s.g)) = 0 := by
      rw [eF, nOpen_ks _ fun r hr => hstD r (List.mem_of_mem_take hr), o1]
      rfl
    have aS : nOpen (cutS l (s.h + s.g)) = (ksOf (((l.map (·.1)).drop (1 + (s.h + s.g))).take
        2)).length := by
      rw [eS, nOpen_ks _ fun r hr => hstD r (List.mem_of_mem_drop (List.mem_of_mem_take hr))]
    have esplit : ksOf (l.map (·.1)) = ksOf (((l.map (·.1)).drop (1 + (s.h + s.g))).take 2) ++
        ksOf ((l.map (·.1)).drop (s.h + s.g + 3)) := by
      have e3 : (l.map (·.1)).drop (s.h + s.g + 3) = ((l.map (·.1)).drop (1 + (s.h + s.g))).drop
          2 := by
        rw [List.drop_drop]
        congr 1
        omega
      rw [e3, ← ksOf_append, List.take_append_drop]
      conv_lhs =>
        rw [← List.take_append_drop (1 + (s.h + s.g)) (l.map (·.1)), ksOf_append, o1,
            List.nil_append]
    show (∀ grp ∈ grpS l (s.h + s.g) gs, ∀ x ∈ grp, x.2 = colW d m.1 x.1) ∧
      ShownFrom next dS b.2.1.1.1 b.2.2 (l.drop (s.h + s.g + 3)) (grpR l (s.h + s.g) gs)
    refine ⟨?_, ?_⟩
    · intro grp hg x hx
      unfold grpS at hg
      rw [aF, List.drop_zero, aS] at hg
      have hT := List.forall₂_take (ksOf (((l.map (·.1)).drop (1 + (s.h + s.g))).take 2)).length hK
      rw [esplit, List.take_left'  rfl] at hT
      obtain ⟨key, hk, hr⟩ := f2_mem_right hT grp hg
      exact treeCol_some d m x.1 x.2 (hS _ (hr x hx) (o2 key hk))
    · refine ih dS b.2.1.1 (n + 1) b.2.2 (l.drop (s.h + s.g + 3)) _ (fun r hr =>
        hst r (List.mem_of_mem_drop hr)) ?_
        (by rw [List.map_drop]; exact o3) hF1 hF2
      unfold grpR
      rw [aF, Nat.zero_add, aS, List.map_drop]
      have hD := List.forall₂_drop (ksOf (((l.map (·.1)).drop (1 + (s.h + s.g))).take 2)).length hK
      rw [esplit, List.drop_left' rfl] at hD
      exact hD

end Desc.K15

#print axioms Desc.K15.keyedIn_of_step
#print axioms Desc.K15.shownFrom_of_keys
