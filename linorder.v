(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Monoid GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Delimit Scope order_scope with O.

(* -------------------------------------------------------------------- *)
Section Extrema.
Context {R : realDomainType} {I : finType} (P : pred I) (F : I -> R).

Hypothesis hP : (exists i, P i).

Local Lemma arg_min_proof :
  exists i, P i && [forall (j | P j), (F i <= F j)%R].
Proof.
pose s := [seq i <- enum I | P i]; pose i0 := xchoose hP.
suff: exists2 i, i \in s & (forall j, j \in s -> (F i <= F j)%R).
+ case=> i; rewrite mem_filter => /andP[Pi _] mini; exists i.
  apply/andP; split=> //; apply/forall_inP => j Pj.
  by apply/mini; rewrite mem_filter Pj mem_enum.
have: s != [::]; first rewrite -has_filter.
+ by apply/hasP; exists i0; [rewrite mem_enum | apply/xchooseP].
elim: s => {i0} // i s ih _; case: (s =P [::]) => [{ih}->|].
+ by exists i => [|j]; rewrite mem_seq1 => // /eqP ->.
move/eqP=> /ih[{ih} j j_in_s ih]; case: (lerP (F i) (F j)).
+ move=> le_FiFj; exists i; first by rewrite mem_head.
  move=> k; rewrite in_cons => /orP[/eqP->//|/ih].
  by apply/(ler_trans le_FiFj).
+ move/ltrW=> le_FjFi; exists j; first by rewrite mem_behead.
  by move=> k; rewrite in_cons => /orP[/eqP->|/ih].
Qed.

Definition arg_minr := nosimpl (xchoose arg_min_proof).

CoInductive extremum_spec : I -> Type :=
  ExtremumSpec i of P i & (forall j, P j -> (F i <= F j)%R)
    : extremum_spec i.

Lemma arg_minrP : extremum_spec arg_minr.
Proof.
by have /andP[Px /forall_inP Plex] := xchooseP arg_min_proof.
Qed.
End Extrema.

(* -------------------------------------------------------------------- *)
Section LinOrderNat.
Context (le : rel nat).

Local Notation "x <= y" := (le x y) : order_scope.

Hypothesis lexx     : reflexive le.
Hypothesis le_asym  : antisymmetric le.
Hypothesis le_trans : transitive le.

Lemma eq_le x y : (x == y) = ((x <= y)%O && (y <= x))%O.
Proof.
by apply/eqP/idP => [->|]; [rewrite lexx | apply/le_asym].
Qed.

Let P n (α : nat -> rat) := forall (i j : 'I_n), α i = α j -> i = j.
Let Q n (α : nat -> rat) := forall (i j : 'I_n), (i <= j)%O -> α i <= α j.
Let R n (α : nat -> rat) := forall i : 'I_n, -1 < α i < 1.

Section Extend.
Context (n : nat) (α : nat -> rat).

Hypothesis (Pα : P n α) (Qα : Q n α) (Rα : R n α).

Local Lemma extend : {β : nat -> rat |
  forall i : 'I_n, β i = α i & [/\ P n.+1 β, Q n.+1 β & R n.+1 β]}.
Proof.
pose En : {set 'I_n} := [set i in 'I_n | (i <= n)%O].
pose Ep : {set 'I_n} := [set i in 'I_n | (n <= i)%O].
have: { q : rat | -1 < q < 1 & [/\
          forall i : 'I_n, i \in Ep -> q < α i ,
          forall i : 'I_n, i \in En -> q > α i &
          forall i : 'I_n, q != α i ] }.
+ have: { q : rat | -1 <= q < 1 & [/\
          forall i : 'I_n, i \in En -> q >= α i &
          forall i : 'I_n, i \in Ep -> q <  α i ] }.
  - case: (set_0Vmem En) => /= [->|nz_En].
    * exists (-1) => //; split=> i; first by rewrite in_set0.
      by move=> _; case/andP: (Rα i).
    have h: exists x, x \in En by case: nz_En => x ?; exists x.
    exists (α (arg_minr (-%R \o α \o val) h)); last split.
    * case: arg_minrP => /= i _ _; case/andP: (Rα i).
      by move/ltrW=> -> ->.
    * move=> i i_En; case: arg_minrP => /= j _.
      by move/(_ _ i_En); rewrite ler_opp2.
    * move=> i i_Ep; case: arg_minrP => /= j j_En _.
      rewrite ltr_neqAle Qα ?andbT; last first.
        move: i_Ep; rewrite in_set => /andP[_ le_ni].
        move: j_En; rewrite in_set => /andP[_ le_jn].
        by apply/(le_trans le_jn le_ni).
      apply/eqP => /Pα eq_ji.
      have {eq_ji} j_Ep: j \in Ep by rewrite eq_ji.
      move: j_Ep j_En; rewrite !in_set => /andP[_ le1] /andP[_ le2].
      have: (val j == n) by rewrite eq_le !(le1, le2).
      by rewrite ltn_eqF // ltn_ord.
  case=> qn /andP[ge_qn le_qn] [qn_En qn_Ep].
  have: { q : rat | -1 < q <= 1 & [/\ q > qn &
          forall i : 'I_n, i \in Ep -> q <= α i ] }.
  - case: (set_0Vmem Ep) => /= [->|nz_Ep].
    * by exists 1 => //; split => // i; rewrite in_set0.
    have h: exists x, x \in Ep by case: nz_Ep => x ?; exists x.
    exists (α (arg_minr (α \o val) h)); last split.
    * case: arg_minrP => /= i _ _; case/andP: (Rα i).
      by move=> -> /ltrW ->.
    * by case: arg_minrP => /= i /qn_Ep.
    by move=> i i_Ep; case: arg_minrP => /= j _ /(_ _ i_Ep).
  case=> qp /andP[ge_qp le_qp] [lt_qn_qp] qp_Ep.
  have qp_En (i : 'I_n): i \in En -> α i < qp.
  - by move=> i_En; apply/(ler_lt_trans (qn_En _ i_En)).
  have: { q : rat | qn < q < qp & forall i : 'I_n, q != α i }.
  - case: (pickP (fun i : 'I_n => qn < α i < qp)) => /= [i cmp_αi|].
    * have h: exists i : 'I_n, qn < α i < qp by exists i.
      pose r := arg_minr (α \o val) h; pose s := (qn + α r) / 2%:R.
      have cmp_s: qn < s < qp; first rewrite /s /r.
        case: arg_minrP => /= j /andP[lt_qn_αj lt_αj_qp] _.
        by case: (midf_lt lt_qn_αj) => ->/= /ltr_trans; apply.
      exists s => // => j; apply/contraTneq: cmp_s.
      rewrite /s /r; case: arg_minrP => /= k /andP[lt_αk gt_αk].
      move/(_ j) => hj /esym αjE; move: hj.
      rewrite αjE; case: (midf_lt lt_αk) => -> /= hk abs.
      move/ltr_trans: hk => -/(_ _ gt_αk) {abs}/abs.
      by rewrite lerNgt; case: (midf_lt lt_αk) => _ ->.
    * move=> h; exists ((qn + qp) / 2%:R).
        by case: (midf_lt lt_qn_qp) => -> ->.
      move=> i; move/negbT: (h i); apply/contraNneq => <-.
      by case: (midf_lt lt_qn_qp) => -> ->.
  case=> q /andP[lt_q gt_q] fresh_q; exists q; last split => //.
  - by rewrite (ler_lt_trans ge_qn lt_q) (ltr_le_trans gt_q le_qp).
  - by move=> i Epi; apply/(ltr_le_trans gt_q (qp_Ep _ Epi)).
  - by move=> i Eni; apply(ler_lt_trans (qn_En _ Eni) lt_q).
case=> q cmp_q [Ep_q En_q fresh_q].
pose β k := if k == n then q else α k.
exists β => [[i /= lt_in]|]; [by rewrite /β ltn_eqF | split].
+ rewrite /P => i j; wlog: i j / (i <= j)%N => [wlog|].
  - case/orP: (leq_total i j) => /wlog //.
    by move=> h1 h2; apply/esym/h1/esym.
  rewrite [i = j](rwP val_eqP); move: i j.
  rewrite -![n.+1]addn1 => i j; case: (splitP j).
  - move=> kj => /= ->; case: (splitP i) => ki; last first.
    * by rewrite ord1 addn0 => ->; rewrite leqNgt ltn_ord.
    by move=> /= ->; rewrite /β ![_ == n]ltn_eqF // => _ /Pα ->.
  move=> /= k; rewrite ord1 addn0 => -> {k} _.
  case: (splitP i) => k /= ->; last by rewrite ord1 addn0.
  by rewrite /β eqxx ltn_eqF // => /esym; apply/contra_eq.
+ rewrite /Q; rewrite -[n.+1]addn1 => i j; case: (splitP j).
  - move=> kj ->; rewrite {2}/β ltn_eqF //; case: (splitP i).
      by move=> ki ->; rewrite /β ltn_eqF //; apply/Qα.
    move=> k; rewrite ord1 addn0 => -> {k}.
    by rewrite /β eqxx => h; apply/ltrW/Ep_q; rewrite inE.
  - move=> k; rewrite ord1 addn0 => -> {k}; rewrite /β eqxx.
    case: (splitP i); last first.
      by move=> k; rewrite ord1 addn0 => ->; rewrite eqxx.
    move=> k -> h; rewrite ltn_eqF //.
    by apply/ltrW/En_q; rewrite inE.
+ rewrite /R; rewrite -addn1 => i; case: (splitP i); last first.
  - by move=> k; rewrite ord1 addn0 => ->; rewrite /β eqxx.
  by move=> j ->; rewrite /β ltn_eqF.
Qed.
End Extend.

(* -------------------------------------------------------------------- *)
Definition ext0 : nat -> rat := fun _ => 0.

Local Lemma ext0_proof : [/\ P 0 ext0, Q 0 ext0 & R 0 ext0].
Proof. by split; case. Qed.

Fixpoint extn_r (n : nat) {struct n}
  : { α : nat -> rat & [/\ P n α, Q n α & R n α] }
:=
  if n is p.+1 then
    let: existT α (And3 p1 p2 p3) := extn_r p in
    let: exist2 β _ w := @extend p α p1 p2 p3 in
    Tagged _ w
  else Tagged _ ext0_proof.

Definition extn (n : nat) := tag (extn_r n.+1) n.

(* -------------------------------------------------------------------- *)
Definition linop : rel nat := [rel n p | extn n <= extn p].

(* -------------------------------------------------------------------- *)
Local Lemma extn_monoS n p :
  (p < n)%N -> tag (extn_r n) p = tag (extn_r n.+1) p.
Proof.
move=> lt_pn /=; case: extn_r => α [w1 w2 w3] /=.
by case: extend => β eq _ /=; apply/esym/(eq (Ordinal lt_pn)).
Qed.

(* -------------------------------------------------------------------- *)
Local Lemma extn_mono n p : (n < p)%N -> extn n = tag (extn_r p) n.
Proof.
elim: p => [|p ih] //; rewrite ltnS leq_eqVlt.
by case/orP => [/eqP<-//|lt_np]; rewrite ih // extn_monoS.
Qed.

(* -------------------------------------------------------------------- *)
Lemma linop_extend n p : (n <= p)%O -> linop n p.
Proof.
move=> lo_np; rewrite /linop /=; pose r := (maxn n p).+1.
have h1: (n < r)%N by rewrite ltnS leq_maxl.
have h2: (p < r)%N by rewrite ltnS leq_maxr.
rewrite (extn_mono h1) (extn_mono h2); case: extn_r => /= α.
by case=> [_ /(_ (Ordinal h1) (Ordinal h2)) h _]; apply/h.
Qed.

End LinOrderNat.

(* -------------------------------------------------------------------- *)
Section LinOrderGen.
Context {T : countType} (le : rel T).

Local Notation "x <= y" := (le x y) : order_scope.

Hypothesis lexx     : reflexive le.
Hypothesis le_asym  : antisymmetric le.
Hypothesis le_trans : transitive le.

Let S (m n : nat) :=
  if m == n then true else
    if   (pickle_inv T m, pickle_inv T n) is (Some m, Some n)
    then (m <= n)%O
    else false.

Theorem lin_order_countable :
  { R : rel T | forall x y, (x <= y)%O -> R x y &
        [/\ total R, reflexive R, antisymmetric R & transitive R] }.
Proof using lexx le_asym le_trans.
have Sxx : reflexive S by move=> x; rewrite /S; rewrite eqxx.
have S_sym : antisymmetric S.
+ move=> /= x y; rewrite /S eq_sym; case: eqP => // _.
  case Ea: pickle_inv => [xa|]; case Eb: pickle_inv => [xb|] => //.
  move/le_asym => h; rewrite -[x](@pickle_invK T) -[y](@pickle_invK T).
  by rewrite Ea Eb /= h.
have S_trans : transitive S.
+ move=> /= x y z; rewrite /S; case: eqP => [<-|]; first by case: eqP.
  move=> /eqP ne_yx; case: eqP => // [<-|]; first by rewrite (negbTE ne_yx).
  move=> /eqP ne_xz; case: eqP => // /eqP ne_yz.
  case Ey: (pickle_inv _ y) => [py|] //;
    case Ez: (pickle_inv _ z) => [pz|] //;
    case Ex: (pickle_inv _ x) => [px|] //.
  by apply/le_trans.
pose linop := linop Sxx S_sym S_trans.
exists [rel x y | linop (pickle x) (pickle y)]; last split.
+ move=> x y le_xy /=; apply/linop_extend; rewrite /S.
  by case: eqP => // _; rewrite !pickleK_inv.
+ by move=> x y; apply/ler_total.
+ by move=> x /=; apply/lerr.
+ move=> x y /ler_asym; set m := pickle x; set n := pickle y.
  have h1: (m < (maxn m n).+1)%N by rewrite ltnS leq_maxl.
  have h2: (n < (maxn m n).+1)%N by rewrite ltnS leq_maxr.
  rewrite (extn_mono Sxx S_sym S_trans h1).
  rewrite (extn_mono Sxx S_sym S_trans h2).
  move=> /=; case: extn_r => /= α [p1 p2 p3] /=.
  case: extend => β _ /= [h _ _] /(h (Ordinal h1) (Ordinal h2)).
  move/val_eqP => /= /eqP; rewrite /m /n.
  by apply/pcan_inj/pickleK_inv.
+ by move=> x y z /=; apply/ler_trans.
Qed.
End LinOrderGen.
