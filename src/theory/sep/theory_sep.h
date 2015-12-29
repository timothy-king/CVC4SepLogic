/*********************                                                        */
/*! \file theory_sep.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Dejan Jovanovic, Clark Barrett
 ** Minor contributors (to current version): Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of sep
 **
 ** Theory of sep.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SEP__THEORY_SEP_H
#define __CVC4__THEORY__SEP__THEORY_SEP_H

#include "theory/theory.h"
#include "util/statistics_registry.h"
#include "theory/uf/equality_engine.h"
#include "context/cdchunk_list.h"
#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdqueue.h"

namespace CVC4 {
namespace theory {

class TheoryModel;

namespace sep {

class TheorySep : public Theory {
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;

  /////////////////////////////////////////////////////////////////////////////
  // MISC
  /////////////////////////////////////////////////////////////////////////////

  private:

  /** True node for predicates = true */
  Node d_true;

  /** True node for predicates = false */
  Node d_false;

  Node mkAnd( std::vector< TNode >& assumptions );

  public:

  TheorySep(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo);
  ~TheorySep();

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

  std::string identify() const { return std::string("TheorySep"); }

  /////////////////////////////////////////////////////////////////////////////
  // PREPROCESSING
  /////////////////////////////////////////////////////////////////////////////

  public:

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);
  Node ppRewrite(TNode atom);

  /////////////////////////////////////////////////////////////////////////////
  // T-PROPAGATION / REGISTRATION
  /////////////////////////////////////////////////////////////////////////////

  private:

  /** Should be called to propagate the literal.  */
  bool propagate(TNode literal);

  /** Explain why this literal is true by adding assumptions */
  void explain(TNode literal, std::vector<TNode>& assumptions);

  public:

  void preRegisterTerm(TNode n);
  void propagate(Effort e);
  Node explain(TNode n);

  public:

  void addSharedTerm(TNode t);
  EqualityStatus getEqualityStatus(TNode a, TNode b);
  void computeCareGraph();

  /////////////////////////////////////////////////////////////////////////////
  // MODEL GENERATION
  /////////////////////////////////////////////////////////////////////////////

  public:

  void collectModelInfo(TheoryModel* m, bool fullModel);

  /////////////////////////////////////////////////////////////////////////////
  // NOTIFICATIONS
  /////////////////////////////////////////////////////////////////////////////

  private:
  public:

  Node getNextDecisionRequest();

  void presolve();
  void shutdown() { }

  /////////////////////////////////////////////////////////////////////////////
  // MAIN SOLVER#include "context/cdhashmap.h"
  /////////////////////////////////////////////////////////////////////////////
  public:

  void check(Effort e);

  private:

  // NotifyClass: template helper class for d_equalityEngine - handles call-back from congruence closure module
  class NotifyClass : public eq::EqualityEngineNotify {
    TheorySep& d_sep;
  public:
    NotifyClass(TheorySep& sep): d_sep(sep) {}

    bool eqNotifyTriggerEquality(TNode equality, bool value) {
      Debug("sep::propagate") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false") << ")" << std::endl;
      // Just forward to sep
      if (value) {
        return d_sep.propagate(equality);
      } else {
        return d_sep.propagate(equality.notNode());
      }
    }

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) {
      Unreachable();
    }

    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
      Debug("sep::propagate") << "NotifyClass::eqNotifyTriggerTermEquality(" << t1 << ", " << t2 << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value) {
        // Propagate equality between shared terms
        return d_sep.propagate(t1.eqNode(t2));
      } else {
        return d_sep.propagate(t1.eqNode(t2).notNode());
      }
      return true;
    }

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) {
      Debug("sep::propagate") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
      d_sep.conflict(t1, t2);
    }

    void eqNotifyNewClass(TNode t) { }
    void eqNotifyPreMerge(TNode t1, TNode t2) { d_sep.eqNotifyPreMerge( t1, t2 ); }
    void eqNotifyPostMerge(TNode t1, TNode t2) { d_sep.eqNotifyPostMerge( t1, t2 ); }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) { }
  };

  /** The notify class for d_equalityEngine */
  NotifyClass d_notify;

  /** Equaltity engine */
  eq::EqualityEngine d_equalityEngine;

  /** Are we in conflict? */
  context::CDO<bool> d_conflict;
  std::vector< Node > d_pending_exp;
  std::vector< Node > d_pending;
  std::vector< int > d_pending_lem;

  /** Conflict when merging constants */
  void conflict(TNode a, TNode b);

  //cache for positive polarity start reduction
  NodeSet d_reduce;
  std::map< Node, std::map< Node, Node > > d_red_conc;
  std::map< Node, std::map< Node, Node > > d_neg_guard;
  //cache for references
  std::map< Node, TypeNode > d_reference_type;
  std::map< Node, std::vector< Node > > d_references;
  /** inferences: maintained to ensure ref count for internally introduced nodes */
  NodeList d_infer;
  NodeList d_infer_exp;
  NodeList d_spatial_assertions;

  std::map< TypeNode, Node > d_base_label;
  std::map< Node, std::map< int, Node > > d_label_map;

  class HeapAssertInfo {
  public:
    HeapAssertInfo( context::Context* c );
    ~HeapAssertInfo(){}
    context::CDO< Node > d_pto;
    context::CDO< bool > d_has_neg_pto;
  };
  std::map< Node, HeapAssertInfo * > d_heap_info;
  HeapAssertInfo * getOrMakeHeapAssertInfo( Node n, bool doMake = false );

  std::map< Node, HeapAssertInfo * > d_eqc_info;
  HeapAssertInfo * getOrMakeEqcInfo( Node n, bool doMake = false );

  //calculate the element type of the heap for spatial assertions
  TypeNode getReferenceType( Node atom );
  TypeNode getReferenceType2( Node atom, Node n, std::map< Node, bool >& visited );
  //get the base label for the spatial assertion
  Node getBaseLabel( TypeNode tn );
  Node getLabel( Node atom, int child, Node lbl );
  Node applyLabel( Node n, Node lbl, std::map< Node, Node >& visited );
  void getLabelChildren( Node atom, Node lbl, std::vector< Node >& children, std::vector< Node >& labels );
  void getSubLabels( Node atom, Node lbl, std::vector< Node >& labels, std::vector< int >& lindex );

  class HeapInfo {
  public:
    HeapInfo() : d_computed(false), d_strict( false ) {}
    //information about the assertions
    std::vector< Node > d_heap_active_assertions;
    std::map< Node, Node > d_wand_to_base_label;
    Node d_heap_pos_pto;
    //information about the model
    bool d_computed;
    bool d_strict;
    std::vector< Node > d_heap_locs;
    std::vector< Node > d_heap_locs_r;
    std::vector< Node > d_heap_locs_model;
    //get value
    Node getValue( TypeNode tn );
  };
  //heap info ( label -> HeapInfo )
  std::map< Node, HeapInfo > d_label_model;

  void debugPrintHeap( HeapInfo& heap, const char * c );
  void validatePto( HeapAssertInfo * ei, Node ei_n );
  void addPto( HeapAssertInfo * ei, Node ei_n, Node p, bool polarity );
  void mergePto( Node p1, Node p2 );
  void computeLabelModel( Node lbl );
  void addHeapLocToLabel( Node lbl, Node atom, Node loc, Node loc_r );

  //hack FIXME
  TheoryModel* d_last_model;
private:
  Node getRepresentative( Node t );
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  /** called when two equivalence classes will merge */
  void eqNotifyPreMerge(TNode t1, TNode t2);
  void eqNotifyPostMerge(TNode t1, TNode t2);

  void sendLemma( std::vector< Node >& ant, Node conc, const char * c, bool infer = false );
  void doPendingFacts();
public:
  eq::EqualityEngine* getEqualityEngine() {
    return &d_equalityEngine;
  }

};/* class TheorySep */

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SEP__THEORY_SEP_H */
