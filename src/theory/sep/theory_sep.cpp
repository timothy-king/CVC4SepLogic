/*********************                                                        */
/*! \file theory_sep.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of sep.
 **
 ** Implementation of the theory of sep.
 **/


#include "theory/sep/theory_sep.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include <map>
#include "theory/rewriter.h"
#include "expr/command.h"
#include "theory/theory_model.h"
#include "theory/sep/options.h"
#include "smt/options.h"
#include "smt/logic_exception.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace sep {

TheorySep::TheorySep(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
  Theory(THEORY_SEP, c, u, out, valuation, logicInfo),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::sep::TheorySep", true),
  d_conflict(c, false),
  d_star_pos_reduce(u),
  d_infer(c),
  d_infer_exp(c)
{
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::SEP_PTO);
  //d_equalityEngine.addFunctionKind(kind::SEP_STAR);
}

TheorySep::~TheorySep() {

}

void TheorySep::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

Node TheorySep::mkAnd( std::vector< TNode >& assumptions ) {
  if( assumptions.empty() ){
    return d_true;
  }else if( assumptions.size()==1 ){
    return assumptions[0];
  }else{
    return NodeManager::currentNM()->mkNode( kind::AND, assumptions );
  }
}

/////////////////////////////////////////////////////////////////////////////
// PREPROCESSING
/////////////////////////////////////////////////////////////////////////////



Node TheorySep::ppRewrite(TNode term) {

  return term;
}


Theory::PPAssertStatus TheorySep::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {

  return PP_ASSERT_STATUS_UNSOLVED;
}


/////////////////////////////////////////////////////////////////////////////
// T-PROPAGATION / REGISTRATION
/////////////////////////////////////////////////////////////////////////////


bool TheorySep::propagate(TNode literal)
{
  Debug("sep") << "TheorySep::propagate(" << literal  << ")" << std::endl;
  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("sep") << "TheorySep::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }
  bool ok = d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }
  return ok;
}/* TheorySep::propagate(TNode) */


void TheorySep::explain(TNode literal, std::vector<TNode>& assumptions) {
  if( literal.getKind()==kind::SEP_LABEL ){
    //labelled assertions are never given to equality engine and should only come from the outside
    assumptions.push_back( literal );
  }else{
    // Do the work
    bool polarity = literal.getKind() != kind::NOT;
    TNode atom = polarity ? literal : literal[0];
    if (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
      d_equalityEngine.explainEquality( atom[0], atom[1], polarity, assumptions, NULL );
    } else {
      d_equalityEngine.explainPredicate( atom, polarity, assumptions );
    }
  }
}

void TheorySep::preRegisterTerm(TNode node){

}


void TheorySep::propagate(Effort e){

}


Node TheorySep::explain(TNode literal)
{
  Debug("sep") << "TheorySep::explain(" << literal << ")" << std::endl;
  std::vector<TNode> assumptions;
  explain(literal, assumptions);
  return mkAnd(assumptions);
}


/////////////////////////////////////////////////////////////////////////////
// SHARING
/////////////////////////////////////////////////////////////////////////////


void TheorySep::addSharedTerm(TNode t) {
  Debug("sep") << "TheorySep::addSharedTerm(" << t << ")" << std::endl;
  d_equalityEngine.addTriggerTerm(t, THEORY_SEP);
}


EqualityStatus TheorySep::getEqualityStatus(TNode a, TNode b) {
  Assert(d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b));
  if (d_equalityEngine.areEqual(a, b)) {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }
  else if (d_equalityEngine.areDisequal(a, b, false)) {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }
  return EQUALITY_UNKNOWN;//FALSE_IN_MODEL;
}


void TheorySep::computeCareGraph() {
  Debug("sharing") << "Theory::computeCareGraph<" << getId() << ">()" << endl;
  for (unsigned i = 0; i < d_sharedTerms.size(); ++ i) {
    TNode a = d_sharedTerms[i];
    TypeNode aType = a.getType();
    for (unsigned j = i + 1; j < d_sharedTerms.size(); ++ j) {
      TNode b = d_sharedTerms[j];
      if (b.getType() != aType) {
        // We don't care about the terms of different types
        continue;
      }
      switch (d_valuation.getEqualityStatus(a, b)) {
      case EQUALITY_TRUE_AND_PROPAGATED:
      case EQUALITY_FALSE_AND_PROPAGATED:
        // If we know about it, we should have propagated it, so we can skip
        break;
      default:
        // Let's split on it
        addCarePair(a, b);
        break;
      }
    }
  }
}


/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////


void TheorySep::collectModelInfo( TheoryModel* m, bool fullModel )
{
  // Send the equality engine information to the model
  //m->assertEqualityEngine(&d_equalityEngine, &termSet);
}

/////////////////////////////////////////////////////////////////////////////
// NOTIFICATIONS
/////////////////////////////////////////////////////////////////////////////


void TheorySep::presolve() {
  Trace("sep") << "Presolving" << std::endl;
}


/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////


void TheorySep::check(Effort e) {
  if (done() && !fullEffort(e)) {
    return;
  }
  
  getOutputChannel().spendResource(options::theoryCheckStep());

  TimerStat::CodeTimer checkTimer(d_checkTime);
  Trace("sep-check") << "Sep::check(): " << e << endl;

  while( !done() && !d_conflict ){
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

    Trace("sep-assert") << "TheorySep::check(): processing " << fact << std::endl;

    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];
    TNode s_atom = atom.getKind()==kind::SEP_LABEL ? atom[0] : atom;
    TNode s_lbl = atom.getKind()==kind::SEP_LABEL ? atom[1] : TNode::null();
    
    if( s_atom.getKind()==kind::SEP_STAR ){
      if( polarity ){
        if( d_star_pos_reduce.find( atom )==d_star_pos_reduce.end() ){
          Trace("sep-lemma-debug") << "Reducing positive star " << atom << std::endl;
          d_star_pos_reduce.insert( atom );
          if( s_atom.getNumChildren()>0 ){
            std::vector< Node > children;
            for( unsigned i=0; i<s_atom.getNumChildren(); i++ ){
              Node lblc = getLabel( s_atom, i, s_lbl );
              Assert( !lblc.isNull() );
              std::map< Node, Node > visited;
              Node lc = applyLabel( s_atom[i], lblc, visited );
              Assert( !lc.isNull() );
              children.push_back( lc );
            }
            Node conc = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( kind::AND, children );
            Node lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, atom, conc );
            Trace("sep-lemma") << "Sep::Lemma : " << lem << std::endl;
            d_out->lemma( lem );
          }
        }
      }else{
        Notice() << "Negated STAR asserted to sep theory: " << fact << std::endl;
      }
    }else{
      Debug("sep") << "Asserting " << atom << " to EE..." << std::endl;
      if( s_atom.getKind()==kind::EQUAL ){
        d_equalityEngine.assertEquality(s_atom, polarity, fact);
      }else{
        d_equalityEngine.assertPredicate(s_atom, polarity, fact);
      }
      Debug("sep") << "Done asserting " << atom << " to EE." << std::endl;
    }
    if( s_atom.getKind()==kind::SEP_STAR || s_atom.getKind()==kind::SEP_PTO || s_atom.getKind()==kind::EMP_STAR ){
      addAssertionToLabel( s_atom, polarity, s_lbl );
      //maybe propagate
      doPendingFacts();
    }
  }

  if( e == EFFORT_FULL && !d_conflict ){
    Assert( d_pending.empty() );
    bool needsCheck = true;
    while( needsCheck ){
      Trace("sep-process") << "Checking heap at full effort..." << std::endl;
      Assert( d_pending.empty() );
      HeapInfo heap;
      bool builtModel = checkHeap( Node::null(), heap );
      Trace("sep-process") << "Done checking heap at full effort, success = " << builtModel;
      Trace("sep-process") << ", facts = " << d_pending.size() << ", lemmas = " << d_pending_lem.size() << ", conflict = " << d_conflict << std::endl;
      if( builtModel && d_pending.empty() ){
        //print heap for debugging TODO
        Trace("sep-model") << "Successfully constructed heap model : " << std::endl;
        debugPrintHeap( heap, "sep-model" );
        Trace("sep-model") << std::endl;
        needsCheck = false;
      }else{
        Assert( d_conflict || !d_pending.empty() );
        needsCheck = !d_conflict && d_pending_lem.empty();
        doPendingFacts();
      }
    }
  }
  Trace("sep-check") << "Sep::check(): " << e << " done, conflict=" << d_conflict.get() << endl;
}


Node TheorySep::getNextDecisionRequest() {
  return Node::null();
}

void TheorySep::conflict(TNode a, TNode b) {
  Trace("sep-conflict") << "Sep::conflict : " << a << " " << b << std::endl;
  Node conflictNode;doPendingFacts();
  if (a.getKind() == kind::CONST_BOOLEAN) {
    conflictNode = explain(a.iffNode(b));
  } else {
    conflictNode = explain(a.eqNode(b));
  }
  d_conflict = true;
  d_out->conflict( conflictNode );
}


TheorySep::HeapAssertInfo::HeapAssertInfo( context::Context* c ) : d_pos_assertions(c), d_neg_assertions(c) {

}

TheorySep::HeapAssertInfo * TheorySep::getOrMakeHeapAssertInfo( Node lbl, bool doMake ) {
  std::map< Node, HeapAssertInfo* >::iterator h_i = d_heap_info.find( lbl );
  if( h_i==d_heap_info.end() ){
    if( doMake ){
      HeapAssertInfo* hi = new HeapAssertInfo( getSatContext() );
      d_heap_info[lbl] = hi;
      return hi;
    }else{
      return NULL;
    }
  }else{
    return (*h_i).second;
  }
}

Node TheorySep::getLabel( Node atom, int child, Node lbl ) {
  std::map< int, Node >::iterator it = d_label_map[atom].find( child );
  if( it==d_label_map[atom].end() ){
    std::stringstream ss;
    if( lbl.isNull() ){
      ss << "__L";
    }else{
      ss << lbl;
    }
    ss << "c" << child;
    Node n_lbl = NodeManager::currentNM()->mkSkolem( ss.str(), NodeManager::currentNM()->booleanType(), "" );
    d_label_map[atom][child] = n_lbl;
    return n_lbl;
  }else{
    return (*it).second;
  }
}

Node TheorySep::applyLabel( Node n, Node lbl, std::map< Node, Node >& visited ) {
  Assert( n.getKind()!=kind::SEP_LABEL );
  if( n.getKind()==kind::SEP_STAR || n.getKind()==kind::SEP_PTO ){
    return NodeManager::currentNM()->mkNode( kind::SEP_LABEL, n, lbl );
  }else if( !n.getType().isBoolean() || n.getNumChildren()==0 ){
    return n;
  }else{
    std::map< Node, Node >::iterator it = visited.find( n );
    if( it==visited.end() ){
      std::vector< Node > children;
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back( n.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node aln = applyLabel( n[i], lbl, visited );
        children.push_back( aln );
        childChanged = childChanged || aln!=n[i];
      }
      Node ret = n;
      if( childChanged ){
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
      visited[n] = ret;
      return ret;
    }else{
      return it->second;
    }
  }
}


bool TheorySep::checkHeap( Node lbl, HeapInfo& heap ) {
  HeapAssertInfo * hi = getOrMakeHeapAssertInfo( lbl );
  if( hi ){
    if( Trace.isOn("sep-solve" ) ){
      Trace("sep-solve") << "Label " << lbl << " has " << hi->d_pos_assertions.size() << " positive assertions : " << std::endl;
      for( NodeList::const_iterator i = hi->d_pos_assertions.begin(); i != hi->d_pos_assertions.end(); ++i ) {
        Trace("sep-solve") << "  " << *i << std::endl;
      }
    }
    
    Node firstTimeAtom;
    for( NodeList::const_iterator ia = hi->d_pos_assertions.begin(); ia != hi->d_pos_assertions.end(); ++ia ) {
      Node atom = (*ia);
      Trace("sep-solve-debug") << "  check atom " << atom << std::endl;
      Assert( atom.getKind()!=kind::SEP_LABEL );
      HeapInfo heap_a;
      if( atom.getKind()==kind::SEP_STAR ){
        bool firstTime = true;
        //construct heap for each child
        for( std::map< int, Node >::iterator itl = d_label_map[atom].begin(); itl != d_label_map[atom].end(); ++itl ){
          Trace("sep-solve-debug") << "  check child #" << itl->first << std::endl;
          if( firstTime ){
            if( !checkHeap( itl->second, heap_a ) ){
              return false;
            }else{
              firstTime = false;
            }
          }else{
            HeapInfo heap_c;
            if( !checkHeap( itl->second, heap_c ) ){
              return false;
            }else{
              //must be disjoint from all others so far
              for( std::map< Node, HeapLoc >::iterator ith = heap_c.d_heap.begin(); ith != heap_c.d_heap.end(); ++ith ){
                std::map< Node, HeapLoc >::iterator itha = heap_a.d_heap.find( ith->first );
                if( itha==heap_a.d_heap.end() ){
                  std::vector< Node > ant;
                  ant.push_back( ith->second.d_lexp );
                  //infer disequalities since disjointedness is entailed
                  for( itha = heap_a.d_heap.begin(); itha != heap_a.d_heap.end(); ++itha ){
                    if( !areDisequal( ith->second.d_exp[0], itha->second.d_exp[0] ) ){
                      ant.push_back( itha->second.d_lexp );
                      Node deq = ith->second.d_exp[0].eqNode( itha->second.d_exp[0] ).negate();
                      sendLemma( ant, deq, "SEP_DEQ", true );
                      ant.pop_back();
                    }
                  }
                  heap_a.d_heap[ith->first] = ith->second;
                }else{
                  //conflict: found non-disjoint pointers over separation STAR
                  std::vector< Node > conf;
                  conf.push_back( ith->second.d_lexp );
                  conf.push_back( itha->second.d_lexp );
                  conf.push_back( ith->second.d_exp[0].eqNode( itha->second.d_exp[0] ) );
                  sendLemma( conf, d_false, "NO_SEP" );
                  return false;
                }
              }
              if( heap_a.d_strict ){
                //if this child is strict, then carry the explanation
                //if this child is not strict, then the parent is not strict
                if( heap_c.d_strict ){
                  heap_a.d_strict_exp.insert( heap_a.d_strict_exp.end(), heap_c.d_strict_exp.begin(), heap_c.d_strict_exp.end() );
                }else{
                  heap_a.d_strict = false;
                  heap_a.d_strict_exp.clear();
                }
              }
            }
          }
        }
      }else if( atom.getKind()==kind::SEP_PTO ){
        Node r1 = getRepresentative( atom[0] );
        Node r2 = getRepresentative( atom[1] );
        heap_a.d_heap[r1].d_val = r2;
        heap_a.d_heap[r1].d_exp = atom;
        heap_a.d_heap[r1].d_lexp = lbl.isNull() ? atom : NodeManager::currentNM()->mkNode( kind::SEP_LABEL, atom, lbl );
        heap_a.d_strict = true;
        heap_a.d_strict_exp.push_back( heap_a.d_heap[r1].d_lexp );
      }else if( atom.getKind()==kind::EMP_STAR ){
        heap_a.d_strict = true;
      }
      
      if( firstTimeAtom.isNull() ){
        Trace("sep-solve-debug") << "  copy to heap..." << std::endl;
        //copy to heap
        for( std::map< Node, HeapLoc >::iterator ita = heap_a.d_heap.begin(); ita != heap_a.d_heap.end(); ++ita ){
          heap.d_heap[ita->first].d_val = ita->second.d_val;
          heap.d_heap[ita->first].d_exp = ita->second.d_exp;
          heap.d_heap[ita->first].d_lexp = ita->second.d_lexp;
        }
        heap.d_strict = heap_a.d_strict;
        heap.d_strict_exp.insert( heap.d_strict_exp.end(), heap_a.d_strict_exp.begin(), heap_a.d_strict_exp.end() );
        firstTimeAtom = atom;
      }else{
        Trace("sep-solve-debug") << "  get to nodes process..." << std::endl;
        std::map< Node, bool > to_process[2];
        for( std::map< Node, HeapLoc >::iterator it = heap.d_heap.begin(); it != heap.d_heap.end(); ++it ){
          to_process[0][it->first] = true;
        }
        Trace("sep-solve-debug") << "  unify with heap..." << std::endl;
          
        //unify with existing heap
        //first, check common indices
        for( std::map< Node, HeapLoc >::iterator ita = heap_a.d_heap.begin(); ita != heap_a.d_heap.end(); ++ita ){
          Trace("sep-solve-debug") << "  unify " << ita->first << std::endl;
          std::map< Node, HeapLoc >::iterator it = heap.d_heap.find( ita->first );
          if( it!=heap.d_heap.end() ){
            Trace("sep-solve-debug") << "  unify common indices : " << it->first << " " << it->second.d_val << " " << ita->second.d_val;
            Trace("sep-solve-debug") << " " << it->second.d_exp << " " << ita->second.d_exp << std::endl;
            if( it->second.d_val!=ita->second.d_val ){
              Assert( !it->second.d_exp.isNull() && !ita->second.d_exp.isNull() );
              Assert( it->second.d_exp.getKind()==kind::SEP_PTO && ita->second.d_exp.getKind()==kind::SEP_PTO );
              //must be equal
              std::vector< Node > ant;
              ant.push_back( it->second.d_lexp );
              ant.push_back( ita->second.d_lexp );
              Node conc = it->second.d_exp[1].eqNode( ita->second.d_exp[1] );
              sendLemma( ant, conc, "INC_UNIFY", true );
            }
            Assert( to_process[0].find( it->first )!=to_process[0].end() );
            to_process[0].erase( it->first );
          }else{
            to_process[1][ita->first] = true;
          }
        }
        Trace("sep-solve-debug") << "  done, to_process : " << to_process[0].size() << " " << to_process[1].size() << "..." << std::endl;
        
        if( !to_process[0].empty() || !to_process[1].empty() ){
          //heaps have different cardinalities
          Trace("sep-solve") << "Must unify heaps for " << std::endl;
          Trace("sep-solve") << "Base HEAP from " << firstTimeAtom << " :" << std::endl;
          debugPrintHeap( heap, "sep-solve" );
          Trace("sep-solve") << "HEAP from " << atom << " :" << std::endl;
          debugPrintHeap( heap_a, "sep-solve" );
          Trace("sep-solve") << std::endl;
          for( unsigned i=0; i<2; i++ ){
            HeapInfo * hi = i==0 ? &heap : &heap_a;
            if( hi->d_strict && !to_process[1-i].empty() ){
              //other heap has a location that does not fit with this strict heap : conflict
              std::vector< Node > ant;
              ant.insert( ant.end(), hi->d_strict_exp.begin(), hi->d_strict_exp.end() );
              //take the first
              ant.push_back( heap_a.d_heap[to_process[1-i].begin()->first].d_lexp );
              //must be equal to one of the unprocessed on this side
              Node un = heap_a.d_heap[to_process[1-i].begin()->first].d_exp[0];
              std::vector< Node > disj;
              for( std::map< Node, bool >::iterator ita = to_process[i].begin(); ita != to_process[i].end(); ++ita ){
                disj.push_back( un.eqNode( heap.d_heap[ita->first].d_exp[0] ) );
              }
              Node conc = disj.empty() ? d_false : ( disj.size()==1 ? disj[0] : NodeManager::currentNM()->mkNode( kind::OR, disj ) );
              sendLemma( ant, conc, "NO_UNIFY" );
              return false;
            }
          }
          if( !heap.d_strict ){
            //combine with the other, regardless of strictness of the other
            for( std::map< Node, bool >::iterator ita = to_process[1].begin(); ita != to_process[1].end(); ++ita ){
              Assert( heap_a.d_heap.find( ita->first )!=heap_a.d_heap.end() );
              heap.d_heap[ita->first].d_val = heap_a.d_heap[ita->first].d_val;
              heap.d_heap[ita->first].d_exp = heap_a.d_heap[ita->first].d_exp;
              heap.d_heap[ita->first].d_lexp = heap_a.d_heap[ita->first].d_lexp;
            }
          }
          heap.d_strict = heap.d_strict || heap_a.d_strict;          
        }
        //Notice() << "Cannot unify heaps (different cardinalities)." << std::endl;
        //d_out->setIncomplete();
      }
    }
    return true;
  }else{
    Trace("sep-solve") << "Label " << lbl << " has no assertions." << std::endl;
    //no constraints
    return true;
  }
}

void TheorySep::addAssertionToLabel( Node atom, bool polarity, Node lbl ) {
  Trace("sep-solve") << "Add assertion " << atom << " to label " << lbl << ", pol = " << polarity << std::endl;
  HeapAssertInfo * hi = getOrMakeHeapAssertInfo( lbl, true );
  if( polarity ){
    //propagate equalities for PTO
    if( atom.getKind()==kind::SEP_PTO ){
      std::vector< Node > exp;
      exp.push_back( atom );
      bool addedLemma = false;
      for( NodeList::const_iterator ia = hi->d_pos_assertions.begin(); ia != hi->d_pos_assertions.end(); ++ia ){
        Node n = (*ia);
        if( n.getKind()==kind::SEP_PTO ){
          exp.push_back( n );
          for( unsigned i=0; i<2; i++ ){
            if( !areEqual( n[i], atom[i] ) ){
              sendLemma( exp, n[i].eqNode( atom[i] ), "PTO_PROP", true );
              addedLemma = true;
            }
          }
          exp.pop_back();
          if( addedLemma ){
            //will be equal to others by transitivity
            break;
          }
        }
      }
    }
    hi->d_pos_assertions.push_back( atom );
  }else{
    d_out->setIncomplete(); //TODO
    hi->d_neg_assertions.push_back( atom );
  }
}

Node TheorySep::getRepresentative( Node t ) {
  if( d_equalityEngine.hasTerm( t ) ){
    return d_equalityEngine.getRepresentative( t );
  }else{
    return t;
  }
}

bool TheorySep::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

bool TheorySep::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool TheorySep::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    if( d_equalityEngine.areDisequal( a, b, false ) ){
      return true;
    }
  } 
  return false;
}

void TheorySep::sendLemma( std::vector< Node >& ant, Node conc, const char * c, bool infer ) {
  Trace("sep-lemma-debug") << "Rewriting inference : " << conc << std::endl;
  conc = Rewriter::rewrite( conc );
  Trace("sep-lemma-debug") << "Got : " << conc << std::endl;
  if( conc!=d_true ){
    if( infer && conc!=d_false ){
      Node ant_n;
      if( ant.empty() ){
        ant_n = d_true;
      }else if( ant.size()==1 ){
        ant_n = ant[0];
      }else{
        ant_n = NodeManager::currentNM()->mkNode( kind::AND, ant );
      }
      Trace("sep-lemma") << "Sep::Infer: " << conc << " from " << ant_n << " by " << c << std::endl;
      d_pending_exp.push_back( ant_n );
      d_pending.push_back( conc );
      d_infer.push_back( ant_n );
      d_infer_exp.push_back( conc );
    }else{
      std::vector< TNode > ant_e;
      for( unsigned i=0; i<ant.size(); i++ ){
        Trace("sep-lemma-debug") << "Explain : " << ant[i] << std::endl;
        explain( ant[i], ant_e );
      }
      Node ant_n;
      if( ant_e.empty() ){
        ant_n = d_true;
      }else if( ant_e.size()==1 ){
        ant_n = ant_e[0];
      }else{
        ant_n = NodeManager::currentNM()->mkNode( kind::AND, ant_e );
      }
      if( conc==d_false ){
        Trace("sep-lemma") << "Sep::Conflict: " << ant_n << " by " << c << std::endl;
        d_out->conflict( ant_n );
        d_conflict = true;
      }else{
        Trace("sep-lemma") << "Sep::Lemma: " << conc << " from " << ant_n << " by " << c << std::endl;
        d_pending_exp.push_back( ant_n );
        d_pending.push_back( conc );
        d_pending_lem.push_back( d_pending.size()-1 );
      }
    }
  }
}

void TheorySep::doPendingFacts() {
  if( d_pending_lem.empty() ){
    for( unsigned i=0; i<d_pending.size(); i++ ){
      if( d_conflict ){
        break;
      }
      Node atom = d_pending[i].getKind()==kind::NOT ? d_pending[i][0] : d_pending[i];
      bool pol = d_pending[i].getKind()!=kind::NOT;
      if( atom.getKind()==kind::EQUAL ){
        d_equalityEngine.assertEquality(atom, pol, d_pending_exp[i]);
      }else{
        d_equalityEngine.assertPredicate(atom, pol, d_pending_exp[i]);
      }
    }
  }else{
    for( unsigned i=0; i<d_pending_lem.size(); i++ ){
      if( d_conflict ){
        break;
      }
      int index = d_pending_lem[i];
      Node lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, d_pending_exp[index], d_pending[index] );
      d_out->lemma( lem );
    }
  }
  d_pending_exp.clear();
  d_pending.clear();
  d_pending_lem.clear();
}

void TheorySep::debugPrintHeap( HeapInfo& heap, const char * c ) {
  Trace(c) << "[ strict : " << heap.d_strict << std::endl;
  for( std::map< Node, HeapLoc >::iterator it = heap.d_heap.begin(); it != heap.d_heap.end(); ++it ){
    Trace(c) << "  " << it->first << " -> " << it->second.d_val << ", from " << it->second.d_exp << std::endl;
  }
  Trace(c) << "]" << std::endl;
}

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
