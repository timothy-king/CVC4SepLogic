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
  d_star_pos_reduce(u)
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
  // Do the work
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions, NULL);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  }
}

void TheorySep::preRegisterTerm(TNode node)
{

}


void TheorySep::propagate(Effort e)
{
  // direct propagation now
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
              std::map< Node, Node > visited;
              Node lc = applyLabel( s_atom[i], lblc, visited );
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
    }
  }

  if( e == EFFORT_FULL && !d_conflict ){
    Trace("sep-process") << "Checking heap at full effort..." << std::endl;
    std::map< Node, Node > heap;
    bool builtModel = checkHeap( Node::null(), heap );
    Trace("sep-process") << "Done checking heap at full effort, success = " << builtModel << std::endl;
    if( builtModel ){
      //print heap
    }
  }
  Trace("sep-check") << "Sep::check(): " << e << " done, conflict=" << d_conflict.get() << endl;
}


Node TheorySep::getNextDecisionRequest() {
  return Node::null();
}

void TheorySep::conflict(TNode a, TNode b) {
  Trace("sep-conflict") << "Sep::conflict : " << a << " " << b << std::endl;
  if (a.getKind() == kind::CONST_BOOLEAN) {
    d_conflictNode = explain(a.iffNode(b));
  } else {
    d_conflictNode = explain(a.eqNode(b));
  }
  d_conflict = true;
}


TheorySep::HeapInfo::HeapInfo( context::Context* c ) : d_pos_assertions(c), d_neg_assertions(c) {

}

TheorySep::HeapInfo * TheorySep::getOrMakeHeapInfo( Node lbl, bool doMake ) {
  std::map< Node, HeapInfo* >::iterator h_i = d_heap_info.find( lbl );
  if( h_i==d_heap_info.end() ){
    if( doMake ){
      HeapInfo* hi = new HeapInfo( getSatContext() );
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
    if( it!=visited.end() ){
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


bool TheorySep::checkHeap( Node lbl, std::map< Node, Node >& heap ) {
  HeapInfo * hi = getOrMakeHeapInfo( lbl );
  if( hi ){
    if( Trace.isOn("sep-solve" ) ){
      Trace("sep-solve") << "Label " << lbl << " has " << hi->d_pos_assertions.size() << " positive assertions : " << std::endl;
      for( NodeList::const_iterator i = hi->d_pos_assertions.begin(); i != hi->d_pos_assertions.end(); ++i ) {
        Trace("sep-solve") << "  " << *i << std::endl;
      }
    }
    
    bool firstTimeAtom = true;
    for( NodeList::const_iterator ia = hi->d_pos_assertions.begin(); ia != hi->d_pos_assertions.end(); ++ia ) {
      Node atom = (*ia);
      std::map< Node, Node > heap_a;
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
            std::map< Node, Node > heap_c;
            if( !checkHeap( itl->second, heap_c ) ){
              return false;
            }else{
              //must be disjoint from all others so far
              for( std::map< Node, Node >::iterator ith = heap_c.begin(); ith != heap_c.end(); ++ith ){
                std::map< Node, Node >::iterator itha = heap_a.find( ith->first );
                if( itha==heap_a.end() ){
                  heap_a[ith->first] = ith->second;
                }else{
                  //conflict: found non-disjoint pointers over separation STAR
                  std::vector< Node > conf;
                  conf.push_back( ith->second );
                  conf.push_back( itha->second );
                  conf.push_back( ith->second[0].eqNode( itha->second[0] ) );
                  sendLemma( conf, d_false, "NO_SEP" );
                  return false;
                }
              }
            }
          }

        }
      }else if( atom.getKind()==kind::SEP_PTO ){
        Node r1 = getRepresentative( atom[0] );
        heap_a[r1] = atom;
      }
      if( firstTimeAtom ){
        //copy to heap
        for( std::map< Node, Node >::iterator it = heap_a.begin(); it != heap_a.end(); ++it ){
          heap[it->first] = it->second;
        }
      }else{
        //unify with existing heap
        //TODO
        return false;
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
  HeapInfo * hi = getOrMakeHeapInfo( lbl, true );
  if( polarity ){
    //TODO?
    hi->d_pos_assertions.push_back( atom );
  }else{
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

void TheorySep::sendLemma( std::vector< Node >& ant, Node conc, const char * c ) {
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
    Node lem = NodeManager::currentNM()->mkNode( kind::IMPLIES, ant_n, conc );
    Trace("sep-lemma") << "Sep::Lemma: " << lem << " by " << c << std::endl;
    d_out->lemma( lem );
  }
}

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
