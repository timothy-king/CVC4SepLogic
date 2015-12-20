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
  d_reduce(u),
  d_infer(c),
  d_infer_exp(c),
  d_spatial_assertions(c)
{
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::SEP_PTO);
  //d_equalityEngine.addFunctionKind(kind::SEP_STAR);
}

TheorySep::~TheorySep() {
  for( std::map< Node, HeapAssertInfo * >::iterator it = d_heap_info.begin(); it != d_heap_info.end(); ++it ){
    delete it->second;
  }
  for( std::map< Node, HeapAssertInfo * >::iterator it = d_eqc_info.begin(); it != d_eqc_info.end(); ++it ){
    delete it->second;
  }
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
  if( literal.getKind()==kind::SEP_LABEL ||
      ( literal.getKind()==kind::NOT && literal[0].getKind()==kind::SEP_LABEL ) ){
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
  m->assertEqualityEngine( &d_equalityEngine );
  //hack FIXME
  d_last_model = m;
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
  if (done() && !fullEffort(e) && e != EFFORT_LAST_CALL) {
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
    bool is_spatial = s_atom.getKind()==kind::SEP_STAR || s_atom.getKind()==kind::SEP_PTO || s_atom.getKind()==kind::EMP_STAR;
    if( is_spatial && s_lbl.isNull() ){
      if( d_reduce.find( fact )==d_reduce.end() ){
        Trace("sep-lemma-debug") << "Reducing unlabelled assertion " << atom << std::endl;
        d_reduce.insert( fact );
        //introduce top-level label, add iff
        TypeNode refType = getReferenceType( s_atom );
        Trace("sep-lemma-debug") << "...reference type is : " << refType << std::endl;
        Node b_lbl = getBaseLabel( refType );
        Node s_atom_new = NodeManager::currentNM()->mkNode( kind::SEP_LABEL, s_atom, b_lbl );
        Node lem;
        if( polarity ){
          lem = NodeManager::currentNM()->mkNode( kind::OR, s_atom.negate(), s_atom_new );
        }else{
          lem = NodeManager::currentNM()->mkNode( kind::OR, s_atom, s_atom_new.negate() );
        }
        Trace("sep-lemma") << "Sep::Lemma : base reduction : " << lem << std::endl;
        d_out->lemma( lem );
      }
    }else{
      //do reductions
      if( is_spatial ){
        if( d_reduce.find( fact )==d_reduce.end() ){
          Trace("sep-lemma-debug") << "Reducing assertion " << fact << std::endl;
          d_reduce.insert( fact );
          Node conc;
          std::map< Node, Node >::iterator its = d_red_conc[s_lbl].find( s_atom );
          if( its==d_red_conc[s_lbl].end() ){
            //make conclusion based on type of assertion
            if( s_atom.getKind()==kind::SEP_STAR ){
              std::vector< Node > children;
              std::vector< Node > labels;
              getStarChildren( s_atom, s_lbl, children, labels );
              Assert( children.size()>1 );
              std::vector< Node > conj;
              //reduction for heap : union, pairwise disjoint
              Node ulem = NodeManager::currentNM()->mkNode( kind::UNION, labels[0], labels[1] );
              for( unsigned i=2; i<labels.size(); i++ ){
                ulem = NodeManager::currentNM()->mkNode( kind::UNION, ulem, labels[i] );
              }
              ulem = s_lbl.eqNode( ulem );
              Trace("sep-lemma-debug") << "Sep::Lemma : star reduction, union : " << ulem << std::endl;
              children.push_back( ulem );
              Node empSet = NodeManager::currentNM()->mkConst(EmptySet(s_lbl.getType().toType()));
              for( unsigned i=0; i<labels.size(); i++ ){
                for( unsigned j=(i+1); j<labels.size(); j++ ){
                  Node s = NodeManager::currentNM()->mkNode( kind::INTERSECTION, labels[i], labels[j] );
                  Node ilem = s.eqNode( empSet );
                  Trace("sep-lemma-debug") << "Sep::Lemma : star reduction, disjoint : " << ilem << std::endl;
                  children.push_back( ilem );
                }
              }
              conc = NodeManager::currentNM()->mkNode( kind::AND, children );
            }else if( s_atom.getKind()==kind::SEP_PTO ){
              conc = s_lbl.eqNode( NodeManager::currentNM()->mkNode( kind::SINGLETON, s_atom[0] ) );
            }else{
              //labeled empty star should be rewritten
              //else if( s_atom.getKind()==kind::EMP_STAR ){
              //  conc = s_lbl.eqNode( NodeManager::currentNM()->mkConst(EmptySet(s_lbl.getType().toType())) );
              //}
              Assert( false );
            }
            d_red_conc[s_lbl][s_atom] = conc;
          }else{
            conc = its->second;
          }
          if( !polarity ){
            // introduce guard, assert positive version
            Trace("sep-lemma-debug") << "Negated spatial constraint asserted to sep theory: " << fact << std::endl;
            d_neg_guard[s_lbl][s_atom] = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "G", NodeManager::currentNM()->booleanType() ) );
            d_neg_guard[s_lbl][s_atom] = getValuation().ensureLiteral( d_neg_guard[s_lbl][s_atom] );
            Trace("sep-lemma-debug") << "Neg guard : " << s_lbl << " " << s_atom << " " << d_neg_guard[s_lbl][s_atom] << std::endl;
            AlwaysAssert( !d_neg_guard[s_lbl][s_atom].isNull() );
            d_out->requirePhase( d_neg_guard[s_lbl][s_atom], true );
            Node lem = NodeManager::currentNM()->mkNode( kind::OR, d_neg_guard[s_lbl][s_atom].negate(), conc );
            Trace("sep-lemma") << "Sep::Lemma : (neg) reduction : " << lem << std::endl;
            d_out->lemma( lem );
          }else{
            //reduce based on implication
            Node lem = NodeManager::currentNM()->mkNode( kind::OR, atom.negate(), conc );
            Trace("sep-lemma") << "Sep::Lemma : reduction : " << lem << std::endl;
            d_out->lemma( lem );
          }
        }
      }
      //assert to equality engine
      if( !is_spatial ){
        Trace("sep-assert") << "Asserting " << atom << ", pol = " << polarity << " to EE..." << std::endl;
        if( s_atom.getKind()==kind::EQUAL ){
          d_equalityEngine.assertEquality(atom, polarity, fact);
        }else{
          d_equalityEngine.assertPredicate(atom, polarity, fact);
        }
        Trace("sep-assert") << "Done asserting " << atom << " to EE." << std::endl;
      }else if( s_atom.getKind()==kind::SEP_PTO ){
        if( polarity ){
          //also propagate equality
          Node eq = s_lbl.eqNode( NodeManager::currentNM()->mkNode( kind::SINGLETON, s_atom[0] ) );
          Trace("sep-assert") << "Asserting implied equality " << eq << " to EE..." << std::endl;
          d_equalityEngine.assertEquality(eq, true, fact);
          Trace("sep-assert") << "Done asserting implied equality " << eq << " to EE." << std::endl;
        }
        //associate the equivalence class of the lhs with this pto
        Node r = getRepresentative( s_atom[0] );
        HeapAssertInfo * ei = getOrMakeEqcInfo( r, true );
        addPto( ei, r, atom, polarity );
      }
      //maybe propagate
      doPendingFacts();
      //add to spatial assertions
      if( !d_conflict && is_spatial ){
        d_spatial_assertions.push_back( fact );
      }
    }
  }

  if( e == EFFORT_LAST_CALL && !d_conflict && !d_valuation.needCheck() ){
    Trace("sep-process") << "Checking heap at full effort..." << std::endl;
    d_label_model.clear();
    //build positive/negative assertion lists for labels
    d_heap_active_assertions.clear();
    d_heap_pos_pto.clear();
    Trace("sep-process") << "--- Current spatial assertions : " << std::endl;
    std::map< Node, bool > assert_active;
    for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
      Node fact = (*i);
      Trace("sep-process") << "  " << fact;
      bool polarity = fact.getKind() != kind::NOT;
      TNode atom = polarity ? fact : fact[0];
      Assert( atom.getKind()==kind::SEP_LABEL );
      TNode s_atom = atom[0];
      TNode s_lbl = atom[1];
      //check whether assertion is active : either polarity=true, or guard is not asserted false
      assert_active[fact] = true;
      if( !polarity ){
        Assert( d_neg_guard[s_lbl].find( s_atom )!=d_neg_guard[s_lbl].end() );
        //check if the guard is asserted positively
        Node guard = d_neg_guard[s_lbl][s_atom];
        bool value;
        if( getValuation().hasSatValue( guard, value ) ) {
          assert_active[fact] = value;
        }
      }
      if( assert_active[fact] ){
        d_heap_active_assertions[s_lbl].push_back( s_atom );
        if( polarity && s_atom.getKind()==kind::SEP_PTO ){
          d_heap_pos_pto[s_lbl] = s_atom;
        }
      }else{
        Trace("sep-process") << " [inactive]";
      }
      Trace("sep-process") << std::endl;
    }
    Trace("sep-process") << "---" << std::endl;
    if(Trace.isOn("sep-eqc")) {
      eq::EqClassesIterator eqcs2_i = eq::EqClassesIterator( &d_equalityEngine );
      Trace("sep-eqc") << "EQC:" << std::endl;
      while( !eqcs2_i.isFinished() ){
        Node eqc = (*eqcs2_i);
        eq::EqClassIterator eqc2_i = eq::EqClassIterator( eqc, &d_equalityEngine );
        Trace("sep-eqc") << "Eqc( " << eqc << " ) : { ";
        while( !eqc2_i.isFinished() ) {
          if( (*eqc2_i)!=eqc ){
            Trace("sep-eqc") << (*eqc2_i) << " ";
          }
          ++eqc2_i;
        }
        Trace("sep-eqc") << " } " << std::endl;
        ++eqcs2_i;
      }
      Trace("sep-eqc") << std::endl;
    }

    if( options::sepCheckNeg() ){
      //compute overall model for all labels
      for( std::map< TypeNode, Node >::iterator it = d_base_label.begin(); it != d_base_label.end(); ++it ){
        computeLabelModel( it->second );
      }
      //process spatial assertions
      for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
        Node fact = (*i);
        bool polarity = fact.getKind() != kind::NOT;
        if( !polarity ){
          Assert( assert_active.find( fact )!=assert_active.end() );
          if( assert_active[fact] ){
            TNode atom = polarity ? fact : fact[0];
            Assert( atom.getKind()==kind::SEP_LABEL );
            TNode s_atom = atom[0];
            TNode s_lbl = atom[1];
            Trace("sep-process") << "--> Active negated atom : " << s_atom << ", lbl = " << s_lbl << std::endl;
            //add refinement lemma
            if( d_label_map.find( s_atom )!=d_label_map.end() ){
              TypeNode tn = getReferenceType( s_atom );
              tn = NodeManager::currentNM()->mkSetType(NodeManager::currentNM()->mkRefType(tn));
              Trace("sep-process") << "    overall model : " << std::endl;
              debugPrintHeap( d_label_model[s_lbl], "sep-process" );
              Trace("sep-process") << std::endl;
              std::map< Node, bool > heap_vals;
              std::map< Node, Node > heap_loc_to_actual;
              for( unsigned j=0; j<d_label_model[s_lbl].d_heap_locs_r.size(); j++ ){
                heap_vals[d_label_model[s_lbl].d_heap_locs_r[j]] = true;
                heap_loc_to_actual[d_label_model[s_lbl].d_heap_locs_r[j]] = d_label_model[s_lbl].d_heap_locs[j];
              }
              std::map< int, Node > mvals;
              std::vector< int > nstrict_children;
              for( std::map< int, Node >::iterator itl = d_label_map[s_atom].begin(); itl != d_label_map[s_atom].end(); ++itl ){
                computeLabelModel( itl->second );
                Node lbl_mval = d_label_model[itl->second].getValue( tn );
                Trace("sep-process") << "  child " << itl->first << " : " << itl->second << ", mval = " << lbl_mval << ", strict = " << d_label_model[itl->second].d_strict << std::endl;
                //take difference from overall
                for( unsigned j=0; j<d_label_model[itl->second].d_heap_locs_r.size(); j++ ){
                  Node loc_r = d_label_model[itl->second].d_heap_locs_r[j];
                  if( heap_vals.find( loc_r )!=heap_vals.end() ){
                    heap_vals.erase( loc_r );
                  }
                }
                // record if non-strict
                if( !d_label_model[itl->second].d_strict ){
                  nstrict_children.push_back( itl->first );
                }
                mvals[itl->first] = lbl_mval;
              }
              Trace("sep-process") << "    non-strict children : ";
              for( unsigned j=0; j<nstrict_children.size(); j++ ){
                Trace("sep-process") << nstrict_children[j] << " ";
              }
              Trace("sep-process") << std::endl;
              bool success;
              if( !heap_vals.empty() ){
                Assert( !nstrict_children.empty() );
                Trace("sep-process") << "    unaccounted locations : ";
                std::vector< Node > locs;
                std::vector< int > loc_to_nstrict;
                for( std::map< Node, bool >::iterator it = heap_vals.begin(); it != heap_vals.end(); ++it ){
                  Assert( heap_loc_to_actual.find( it->first )!=heap_loc_to_actual.end() );
                  Node ac_loc = heap_loc_to_actual[it->first];
                  Trace("sep-process") << ac_loc << " ";
                  locs.push_back( ac_loc );
                  loc_to_nstrict.push_back( 0 );
                }
                Trace("sep-process") << std::endl;
                loc_to_nstrict[0] = -1;

                std::map< int, std::vector< Node > > models;
                for( std::map< int, Node >::iterator itl = d_label_map[s_atom].begin(); itl != d_label_map[s_atom].end(); ++itl ){
                  models[itl->first].insert( models[itl->first].end(), d_label_model[itl->second].d_heap_locs.begin(), d_label_model[itl->second].d_heap_locs.end() );
                }
                bool success2;
                do{
                  //increment loc_to_nstrict vector
                  success2 = false;
                  Trace("sep-process-debug2") << "Increment loc_to_nstrict..." << std::endl;
                  int index = 0;
                  do{
                    loc_to_nstrict[index]++;
                    if( loc_to_nstrict[index]<(int)nstrict_children.size() ){
                      success2 = true;
                    }else{
                      loc_to_nstrict[index] = 0;
                      index++;
                    }
                  }while( !success2 && index<(int)loc_to_nstrict.size() );

                  success = false;
                  if( success2 ){
                    Trace("sep-process-debug2") << "Populate model..." << std::endl;
                    //populate models
                    for( unsigned j=0; j<loc_to_nstrict.size(); j++ ){
                      models[nstrict_children[loc_to_nstrict[j]]].push_back( locs[j] );
                    }
                    //check whether instantiation exists
                    Trace("sep-process-debug2") << "Check exists inst..." << std::endl;
                    success = !d_neg_inst_trie[s_atom].existsInst( s_atom.getNumChildren(), models );
                    for( unsigned j=0; j<loc_to_nstrict.size(); j++ ){
                      models[nstrict_children[loc_to_nstrict[j]]].pop_back();
                    }
                  }
                }while( !success && success2 );

                if( success ){
                  //add to mvals
                  for( unsigned j=0; j<loc_to_nstrict.size(); j++ ){
                    Trace("sep-process") << "    -> Add " << locs[j] << " to child #" << nstrict_children[loc_to_nstrict[j]] << std::endl;
                    mvals[nstrict_children[loc_to_nstrict[j]]] = mvals[nstrict_children[loc_to_nstrict[j]]].getKind()==kind::EMPTYSET ? locs[j] : NodeManager::currentNM()->mkNode( kind::UNION, mvals[nstrict_children[loc_to_nstrict[j]]], locs[j] );
                  }
                }
              }else{
                success = true;
                Trace("sep-process-debug") << "    children match the overall model." << std::endl;
              }
              if( success ){
                std::vector< Node > conc;
                for( std::map< int, Node >::iterator itl = d_label_map[s_atom].begin(); itl != d_label_map[s_atom].end(); ++itl ){
                  std::map< Node, Node > visited;
                  Node c = applyLabel( s_atom[itl->first], mvals[itl->first], visited );
                  Trace("sep-process-debug") << "    applied inst : " << c << std::endl;
                  conc.push_back( c.negate() );
                }
                // Now, assert model-instantiated implication based on the negation
                Node o_b_lbl_mval = d_label_model[s_lbl].getValue( tn );
                std::vector< Node > lemc;
                lemc.push_back( atom );
                lemc.push_back( s_lbl.eqNode( o_b_lbl_mval ).negate() );
                lemc.insert( lemc.end(), conc.begin(), conc.end() );
                Node lem = NodeManager::currentNM()->mkNode( kind::OR, lemc );
                Trace("sep-lemma") << "Sep::Lemma : negated star refinement : " << lem << std::endl;
                d_out->lemma( lem );
              }else{
                Trace("sep-process") << "Sep::WARNING : could not find instantiation!!! " << std::endl;
                d_out->setIncomplete();
              }
            }else{
              Trace("sep-process-debug") << "  no children." << std::endl;
              Assert( s_atom.getKind()==kind::SEP_PTO );
            }
          }
        }
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


TheorySep::HeapAssertInfo::HeapAssertInfo( context::Context* c ) : d_pto(c), d_has_neg_pto(c,false) {

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

TheorySep::HeapAssertInfo * TheorySep::getOrMakeEqcInfo( Node n, bool doMake ) {
  std::map< Node, HeapAssertInfo* >::iterator e_i = d_eqc_info.find( n );
  if( e_i==d_eqc_info.end() ){
    if( doMake ){
      HeapAssertInfo* ei = new HeapAssertInfo( getSatContext() );
      d_eqc_info[n] = ei;
      return ei;
    }else{
      return NULL;
    }
  }else{
    return (*e_i).second;
  }
}

TypeNode TheorySep::getReferenceType( Node atom ) {
  std::map< Node, TypeNode >::iterator it = d_reference_type.find( atom );
  if( it==d_reference_type.end() ){
    std::map< Node, bool > visited;
    TypeNode tn = getReferenceType2( atom, atom, visited );
    if( tn.isNull() ){
      tn = NodeManager::currentNM()->booleanType();
    }
    d_reference_type[atom] = tn;
    return tn;
  }else{
    return it->second;
  }
}

TypeNode TheorySep::getReferenceType2( Node atom, Node n, std::map< Node, bool >& visited ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==kind::SEP_PTO ){
      //if( std::find( d_references[atom].begin(), d_references[atom].end(), n[0] )==d_references.end() ){
      //  d_references[atom].push_back( n[0] );
      //}
      return n[1].getType();
    }else{
      //TypeNode otn;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        TypeNode tn = getReferenceType2( atom, n[i], visited );
        if( !tn.isNull() ){
          //otn = tn;
          return tn;
        }
      }
      //return otn;
    }
  }
  return TypeNode::null();
}

Node TheorySep::getBaseLabel( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_base_label.find( tn );
  if( it==d_base_label.end() ){
    std::stringstream ss;
    ss << "__Lb";
    TypeNode ltn = NodeManager::currentNM()->mkSetType(NodeManager::currentNM()->mkRefType(tn));
    Node n_lbl = NodeManager::currentNM()->mkSkolem( ss.str(), ltn, "" );
    d_base_label[tn] = n_lbl;
    return n_lbl;
  }else{
    return it->second;
  }
}

Node TheorySep::getLabel( Node atom, int child, Node lbl ) {
  std::map< int, Node >::iterator it = d_label_map[atom].find( child );
  if( it==d_label_map[atom].end() ){
    TypeNode refType = getReferenceType( atom );
    std::stringstream ss;
    //if( lbl.isNull() ){
    //}else{
    //  ss << lbl;
    //}
    ss << "__Lc" << child;
    TypeNode ltn = NodeManager::currentNM()->mkSetType(NodeManager::currentNM()->mkRefType(refType));
    Node n_lbl = NodeManager::currentNM()->mkSkolem( ss.str(), ltn, "" );
    d_label_map[atom][child] = n_lbl;
    return n_lbl;
  }else{
    return (*it).second;
  }
}

Node TheorySep::applyLabel( Node n, Node lbl, std::map< Node, Node >& visited ) {
  Assert( n.getKind()!=kind::SEP_LABEL );
  if( n.getKind()==kind::SEP_STAR || n.getKind()==kind::SEP_PTO || n.getKind()==kind::EMP_STAR ){
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

void TheorySep::getStarChildren( Node atom, Node lbl, std::vector< Node >& children, std::vector< Node >& labels ) {
  for( unsigned i=0; i<atom.getNumChildren(); i++ ){
    Node lblc = getLabel( atom, i, lbl );
    Assert( !lblc.isNull() );
    std::map< Node, Node > visited;
    Node lc = applyLabel( atom[i], lblc, visited );
    Assert( !lc.isNull() );
    children.push_back( lc );
    labels.push_back( lblc );
  }
  Assert( children.size()>1 );
}

void TheorySep::computeLabelModel( Node lbl ) {
  if( d_label_model.find( lbl )==d_label_model.end() ){
    //Node v_val = d_valuation.getModelValue( s_lbl );
    //hack FIXME
    Node v_val = d_last_model->getRepresentative( lbl );
    Trace("sep-process-model-debug") << "    model value (from valuation) for " << lbl << " : " << v_val << std::endl;
    if( v_val.getKind()!=kind::EMPTYSET ){
      while( v_val.getKind()==kind::UNION ){
        Assert( v_val[0].getKind()==kind::SINGLETON );
        d_label_model[lbl].d_heap_locs_model.push_back( v_val[0] );
        v_val = v_val[1];
      }
      Assert( v_val.getKind()==kind::SINGLETON );
      d_label_model[lbl].d_heap_locs_model.push_back( v_val );
    }

    d_label_model[lbl].d_strict = false;
    std::map< Node, Node >::iterator itap = d_heap_pos_pto.find( lbl );
    if( itap!=d_heap_pos_pto.end() ){
      Node atom = itap->second;
      //d_label_model[lbl].d_heap[atom[0]].d_val = atom[1];
      //Node r = getRepresentative( atom[0] );
      Node r = d_last_model->getRepresentative( atom[0] );
      Trace("sep-process-model") << "Sep:Model : pto for " << lbl << " : " << atom << ", r=" << r << std::endl;
      d_label_model[lbl].d_heap_locs.push_back( NodeManager::currentNM()->mkNode( kind::SINGLETON, atom[0] ) );
      d_label_model[lbl].d_heap_locs_r.push_back( NodeManager::currentNM()->mkNode( kind::SINGLETON, r ) );
      d_label_model[lbl].d_strict = true;
    }else{
      std::map< Node, std::vector< Node > >::iterator ita = d_heap_active_assertions.find( lbl );
      if( ita!=d_heap_active_assertions.end() ){
        for( unsigned ia = 0; ia<ita->second.size(); ++ia ) {
          Node atom = ita->second[ia];
          Trace("sep-process-model-debug") << "  atom for label " << lbl << " : " << atom << std::endl;
          Assert( atom.getKind()!=kind::SEP_LABEL );
          if( atom.getKind()==kind::SEP_STAR ){
            //compute model for each child, take union, which is guarenteed to be disjoint
            bool isStrict = true;
            //store the current locations
            std::map< Node, Node > curr_locs;
            for( unsigned j=0; j<d_label_model[lbl].d_heap_locs_r.size(); j++ ){
              curr_locs[d_label_model[lbl].d_heap_locs_r[j]] = d_label_model[lbl].d_heap_locs[j];
            }
            std::vector< Node > new_locs;
            std::vector< Node > new_locs_r;
            for( std::map< int, Node >::iterator itl = d_label_map[atom].begin(); itl != d_label_map[atom].end(); ++itl ){
              Trace("sep-process-model-debug") << "  child " << itl->first << " of atom " << atom << " : " << itl->second << std::endl;
              computeLabelModel( itl->second );
              for( unsigned j=0; j<d_label_model[itl->second].d_heap_locs_r.size(); j++ ){
                Node loc = d_label_model[itl->second].d_heap_locs[j];
                Node loc_r = d_label_model[itl->second].d_heap_locs_r[j];
                if( std::find( d_label_model[lbl].d_heap_locs_r.begin(), d_label_model[lbl].d_heap_locs_r.end(), loc_r )==d_label_model[lbl].d_heap_locs_r.end() ){
                  new_locs.push_back( loc );
                  new_locs_r.push_back( loc_r );
                  d_label_model[lbl].d_heap_locs.push_back( loc );
                  d_label_model[lbl].d_heap_locs_r.push_back( loc_r );
                }else{
                  Assert( curr_locs.find( loc_r )!=curr_locs.end() );
                  curr_locs.erase( loc_r );
                }
              }
              isStrict = isStrict && d_label_model[itl->second].d_strict;
            }
            //add existing heap locations to this atom
            for( std::map< Node, Node >::iterator itcl = curr_locs.begin(); itcl != curr_locs.end(); ++itcl ){
              addHeapLocToLabel( lbl, atom, itcl->second, itcl->first );
            }
            //add new heap locations to other atoms
            for( unsigned k=0; k<ia; k++ ){
              for( unsigned j=0; j<new_locs.size(); j++ ){
                addHeapLocToLabel( lbl, ita->second[k], new_locs[j], new_locs_r[j] );
              }
            }
            d_label_model[lbl].d_strict = d_label_model[lbl].d_strict || isStrict;
          }
        }
      }else{
        // no constraints
      }
      if( Trace.isOn("sep-process-model") ){
        Trace("sep-process-model") << "Sep:Model : locs for " << lbl << " : ";
        for( unsigned j=0; j<d_label_model[lbl].d_heap_locs.size(); j++ ){
          Trace("sep-process-model") << d_label_model[lbl].d_heap_locs[j] << " ";
        }
        Trace("sep-process-model") << std::endl;
      }
    }
  }
}

void TheorySep::addHeapLocToLabel( Node lbl, Node atom, Node loc, Node loc_r ) {
  Assert( d_label_model.find( lbl )!=d_label_model.end() );
  Trace("sep-process-model-debug") << "Sep:Model : Add location " << loc << ", r=" << loc_r << ", to atom " << atom << " with label " << lbl << std::endl;
  if( atom.getKind()==kind::SEP_STAR ){
    //if it is in the label model of a child, recurse
    for( std::map< int, Node >::iterator itl = d_label_map[atom].begin(); itl != d_label_map[atom].end(); ++itl ){
      Assert( d_label_model.find( itl->second )!=d_label_model.end() );
      if( std::find( d_label_model[itl->second].d_heap_locs_model.begin(),
                     d_label_model[itl->second].d_heap_locs_model.end(), loc_r )!=d_label_model[itl->second].d_heap_locs_model.end() ){
        Node c_lbl = itl->second;
        Trace("sep-process-model-debug") << "...add to child : " << c_lbl << std::endl;
        d_label_model[c_lbl].d_heap_locs.push_back( loc );
        d_label_model[c_lbl].d_heap_locs_r.push_back( loc_r );
        std::map< Node, std::vector< Node > >::iterator ita = d_heap_active_assertions.find( c_lbl );
        if( ita!=d_heap_active_assertions.end() ){
          for( unsigned j=0; j<ita->second.size(); j++ ){
            addHeapLocToLabel( c_lbl, ita->second[j], loc, loc_r );
          }
        }
        return;
      }
    }
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

void TheorySep::eqNotifyPreMerge(TNode t1, TNode t2) {

}

void TheorySep::eqNotifyPostMerge(TNode t1, TNode t2) {
  HeapAssertInfo * e2 = getOrMakeEqcInfo( t2, false );
  if( e2 && ( !e2->d_pto.get().isNull() || e2->d_has_neg_pto.get() ) ){
    HeapAssertInfo * e1 = getOrMakeEqcInfo( t1, true );
    if( !e2->d_pto.get().isNull() ){
      if( !e1->d_pto.get().isNull() ){
        Trace("sep-pto-debug") << "While merging " << t1 << " " << t2 << ", merge pto." << std::endl;
        mergePto( e1->d_pto.get(), e2->d_pto.get() );
      }else{
        e1->d_pto.set( e2->d_pto.get() );
      }
    }
    e1->d_has_neg_pto.set( e1->d_has_neg_pto.get() || e2->d_has_neg_pto.get() );
    //validate
    validatePto( e1, t1 );
  }
}

void TheorySep::validatePto( HeapAssertInfo * ei, Node ei_n ) {
  if( !ei->d_pto.get().isNull() && ei->d_has_neg_pto.get() ){
    for( NodeList::const_iterator i = d_spatial_assertions.begin(); i != d_spatial_assertions.end(); ++i ) {
      Node fact = (*i);
      bool polarity = fact.getKind() != kind::NOT;
      if( !polarity ){
        TNode atom = polarity ? fact : fact[0];
        Assert( atom.getKind()==kind::SEP_LABEL );
        TNode s_atom = atom[0];
        if( s_atom.getKind()==kind::SEP_PTO ){
          if( areEqual( s_atom[0], ei_n ) ){
            addPto( ei, ei_n, atom, false );
          }
        }
      }
    }
    //we have now processed all pending negated pto
    ei->d_has_neg_pto.set( false );
  }
}

void TheorySep::addPto( HeapAssertInfo * ei, Node ei_n, Node p, bool polarity ) {
  Trace("sep-pto") << "Add pto : " << p << ", pol = " << polarity << " to eqc " << ei_n << std::endl;
  if( !ei->d_pto.get().isNull() ){
    if( polarity ){
      Trace("sep-pto-debug") << "...eqc " << ei_n << " already has pto " << ei->d_pto.get() << ", merge." << std::endl;
      mergePto( ei->d_pto.get(), p );
    }else{
      Node pb = ei->d_pto.get();
      Trace("sep-pto") << "Process positive/negated pto : " << " " << pb << " " << p << std::endl;
      Assert( pb.getKind()==kind::SEP_LABEL && pb[0].getKind()==kind::SEP_PTO );
      Assert( p.getKind()==kind::SEP_LABEL && p[0].getKind()==kind::SEP_PTO );
      Assert( areEqual( pb[0][0], p[0][0] ) );
      std::vector< Node > exp;
      if( pb[0][0]!=p[0][0] ){
        exp.push_back( pb[0][0].eqNode( p[0][0] ) );
      }
      exp.push_back( pb );
      exp.push_back( p.negate() );
      std::vector< Node > conc;
      if( pb[0][1]!=p[0][1] ){
        conc.push_back( pb[0][1].eqNode( p[0][1] ).negate() );
      }
      if( pb[1]!=p[1] ){
        conc.push_back( pb[1].eqNode( p[1] ).negate() );
      }
      Node n_conc = conc.empty() ? d_false : ( conc.size()==1 ? conc[0] : NodeManager::currentNM()->mkNode( kind::OR, conc ) );
      sendLemma( exp, n_conc, "PTO_NEG_PROP" );
    }
  }else{
    if( polarity ){
      ei->d_pto.set( p );
      validatePto( ei, ei_n );
    }else{
      ei->d_has_neg_pto.set( true );
    }
  }
}

void TheorySep::mergePto( Node p1, Node p2 ) {
  Trace("sep-lemma-debug") << "Merge pto : " << p1 << " " << p2 << std::endl;
  Assert( p1.getKind()==kind::SEP_LABEL && p1[0].getKind()==kind::SEP_PTO );
  Assert( p2.getKind()==kind::SEP_LABEL && p2[0].getKind()==kind::SEP_PTO );
  if( !areEqual( p1[0][1], p2[0][1] ) ){
    std::vector< Node > exp;
    if( p1[0][0]!=p2[0][0] ){
      Assert( areEqual( p1[0][0], p2[0][0] ) );
      exp.push_back( p1[0][0].eqNode( p2[0][0] ) );
    }
    exp.push_back( p1 );
    exp.push_back( p2 );
    sendLemma( exp, p1[0][1].eqNode( p2[0][1] ), "PTO_PROP", true );
  }
}

void TheorySep::sendLemma( std::vector< Node >& ant, Node conc, const char * c, bool infer ) {
  Trace("sep-lemma-debug") << "Do rewrite on inference : " << conc << std::endl;
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
      Trace("sep-pending") << "Sep : Assert to EE : " << atom << ", pol = " << pol << std::endl;
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
      Trace("sep-pending") << "Sep : Lemma : " << lem << std::endl;
    }
  }
  d_pending_exp.clear();
  d_pending.clear();
  d_pending_lem.clear();
}

void TheorySep::debugPrintHeap( HeapInfo& heap, const char * c ) {
  Trace(c) << "[ strict : " << heap.d_strict << std::endl;
  //for( std::map< Node, HeapLoc >::iterator it = heap.d_heap.begin(); it != heap.d_heap.end(); ++it ){
  //  Trace(c) << "  " << it->first << " -> " << it->second.d_val << ", from " << it->second.d_exp << std::endl;
  //}
  Trace(c) << "  ";
  for( unsigned j=0; j<heap.d_heap_locs.size(); j++ ){
    Trace(c) << heap.d_heap_locs[j] << " ";
  }
  Trace(c) << std::endl;
  Trace(c) << "]" << std::endl;
}

Node TheorySep::HeapInfo::getValue( TypeNode tn ) {
  if( d_heap_locs.empty() ){
    return NodeManager::currentNM()->mkConst(EmptySet(tn.toType()));
  }else if( d_heap_locs.size()==1 ){
    return d_heap_locs[0];
  }else{
    Node curr = NodeManager::currentNM()->mkNode( kind::UNION, d_heap_locs[0], d_heap_locs[1] );
    for( unsigned j=2; j<d_heap_locs.size(); j++ ){
      curr = NodeManager::currentNM()->mkNode( kind::UNION, curr, d_heap_locs[j] );
    }
    return curr;
  }
}

bool TheorySep::InstTrie::existsInst( int nchildren, std::map< int, std::vector< Node > >& models ) {
  std::map< int, std::vector< Node > > sorted_models;
  for( std::map< int, std::vector< Node > >::iterator it = models.begin(); it != models.end(); ++it ){
    sorted_models[it->first].insert( sorted_models[it->first].end(), it->second.begin(), it->second.end() );
    std::sort( sorted_models[it->first].begin(), sorted_models[it->first].end() );
  }
  return existsInst2( nchildren, sorted_models, 0, 0 );
}

bool TheorySep::InstTrie::existsInst2( int nchildren, std::map< int, std::vector< Node > >& models, int index, int sindex ) {
  if( index==nchildren ){
    bool ret = d_data;
    d_data = true;
    return ret;
  }else{
    if( sindex==(int)models[index].size() ){
      return d_children[Node::null()].existsInst2( nchildren, models, index+1, 0 );
    }else{
      return d_children[models[index][sindex]].existsInst2( nchildren, models, index, sindex+1 );
    }
  }
}

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
