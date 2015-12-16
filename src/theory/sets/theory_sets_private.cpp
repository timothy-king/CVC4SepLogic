/*********************                                                        */
/*! \file theory_sets_private.cpp
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Sets theory implementation.
 **/

#include <boost/foreach.hpp>

#include "theory/theory_model.h"
#include "theory/sets/scrutinize.h"
#include "theory/sets/theory_sets.h"
#include "theory/sets/theory_sets_private.h"

#include "theory/sets/options.h"
#include "theory/sets/expr_patterns.h" // ONLY included here

#include "util/emptyset.h"
#include "util/result.h"

using namespace std;
using namespace CVC4::expr::pattern;

namespace CVC4 {
namespace theory {
namespace sets {

const char* element_of_str = " \u2208 ";

/**************************** TheorySetsPrivate *****************************/
/**************************** TheorySetsPrivate *****************************/
/**************************** TheorySetsPrivate *****************************/

void TheorySetsPrivate::check(Theory::Effort level) {

  while(!d_external.done() && !d_conflict) {
    // Get all the assertions
    Assertion assertion = d_external.get();
    TNode fact = assertion.assertion;

    Debug("sets") << "\n\n[sets] TheorySetsPrivate::check(): processing "
                  << fact << std::endl;

    bool polarity = fact.getKind() != kind::NOT;
    TNode atom = polarity ? fact : fact[0];

    if (!assertion.isPreregistered) {
      if (atom.getKind() == kind::EQUAL) {
        if (!d_equalityEngine.hasTerm(atom[0])) {
          Assert(atom[0].isConst());
          d_equalityEngine.addTerm(atom[0]);
          d_termInfoManager->addTerm(atom[0]);
        }
        if (!d_equalityEngine.hasTerm(atom[1])) {
          Assert(atom[1].isConst());
          d_equalityEngine.addTerm(atom[1]);
          d_termInfoManager->addTerm(atom[1]);
        }
      }
    }

    // Solve each
    switch(atom.getKind()) {
    case kind::EQUAL:
      Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
                    << "be equal to " << atom[1] << std::endl;
      assertEquality(fact, fact, /* learnt = */ false);
      break;

    case kind::MEMBER:
      Debug("sets") << atom[0] << " should " << (polarity ? "":"NOT ")
                    << "be in " << atom[1] << std::endl;
      assertMemebership(fact, fact, /* learnt = */ false);
      break;

    default:
      Unhandled(fact.getKind());
    }
    finishPropagation();

    Debug("sets") << "[sets]  in conflict = " << d_conflict << std::endl;
    // Assert( d_conflict ^ d_equalityEngine.consistent() );
    // ^ doesn't hold when we propagate equality/disequality between shared terms
    // and that leads to conflict (externally).
    if(d_conflict) { return; }
    Debug("sets") << "[sets]  is complete = " << isComplete() << std::endl;
  }

  if( (level == Theory::EFFORT_FULL || options::setsEagerLemmas() ) && !isComplete()) {
    d_external.d_out->lemma(getLemma());
    return;
  }

  // if we are here, there is no conflict and we are complete
  if(Debug.isOn("sets-scrutinize")) { d_scrutinize->postCheckInvariants(); }

  return;
}/* TheorySetsPrivate::check() */


void TheorySetsPrivate::assertEquality(TNode fact, TNode reason, bool learnt)
{
  Debug("sets-assert") << "\n[sets-assert] adding equality: " << fact
                       << ", " << reason
                       << ", " << learnt << std::endl;

  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];

  // fact already holds
  if( holds(atom, polarity) ) {
    Debug("sets-assert") << "[sets-assert]   already present, skipping" << std::endl;
    return;
  }

  // assert fact & check for conflict
  if(learnt) {
    registerReason(reason, /*save=*/ true);
  }
  d_equalityEngine.assertEquality(atom, polarity, reason);

  if(!d_equalityEngine.consistent()) {
    Debug("sets-assert") << "[sets-assert]   running into a conflict" << std::endl;
    d_conflict = true;
    return;
  }

  if(!polarity && atom[0].getType().isSet()) {
    addToPending(atom);
  }

}/* TheorySetsPrivate::assertEquality() */


void TheorySetsPrivate::assertMemebership(TNode fact, TNode reason, bool learnt)
{
  Debug("sets-assert") << "\n[sets-assert] adding membership: " << fact
                       << ", " << reason
                       << ", " << learnt << std::endl;

  bool polarity = fact.getKind() == kind::NOT ? false : true;
  TNode atom = polarity ? fact : fact[0];

  // fact already holds
  if( holds(atom, polarity) ) {
    Debug("sets-assert") << "[sets-assert]   already present, skipping" << std::endl;
    return;
  }

  // assert fact & check for conflict
  if(learnt) {
    registerReason(reason, true);
  }
  d_equalityEngine.assertPredicate(atom, polarity, reason);

  if(!d_equalityEngine.consistent()) {
    Debug("sets-assert") << "[sets-assert]   running into a conflict" << std::endl;
    d_conflict = true;
    return;
  }

  // update term info data structures
  d_termInfoManager->notifyMembership(fact);

  // propagation
  TNode x = d_equalityEngine.getRepresentative(atom[0]);
  eq::EqClassIterator j(d_equalityEngine.getRepresentative(atom[1]),
                        &d_equalityEngine);
  TNode S = (*j);
  Node cur_atom = MEMBER(x, S);

  /**
   * It is sufficient to do emptyset propagation outside the loop as
   * constant term is guaranteed to be class representative.
   */
  if(polarity && S.getKind() == kind::EMPTYSET) {
    Debug("sets-prop") << "[sets-prop]  something in empty set? conflict."
                       << std::endl;
    learnLiteral(cur_atom, false, cur_atom);
    Assert(d_conflict);
    return;
  }

  /**
   * Disequality propagation if element type is set
   */
  if(x.getType().isSet()) {
    if(polarity) {
      const CDTNodeList* l = d_termInfoManager->getNonMembers(S);
      for(typeof(l->begin()) it = l->begin(); it != l->end(); ++it) {
        TNode n = *it;
        learnLiteral( /* atom = */ EQUAL(x, n),
                      /* polarity = */ false,
                      /* reason = */ AND( MEMBER(x, S), NOT( MEMBER(n, S)) ) );
      }
    } else {
      const CDTNodeList* l = d_termInfoManager->getMembers(S);
      for(typeof(l->begin()) it = l->begin(); it != l->end(); ++it) {
        TNode n = *it;
        learnLiteral( /* atom = */ EQUAL(x, n),
                      /* polarity = */ false,
                      /* reason = */ AND( NOT(MEMBER(x, S)), MEMBER(n, S)) );
      }
    }
  }

  for(; !j.isFinished(); ++j) {
    TNode S = (*j);
    Node cur_atom = MEMBER(x, S);

    // propagation : children
    Debug("sets-prop") << "[sets-prop] Propagating 'down' for "
                       << x << element_of_str << S << std::endl;
    if(S.getKind() == kind::UNION ||
       S.getKind() == kind::INTERSECTION ||
       S.getKind() == kind::SETMINUS ||
       S.getKind() == kind::SINGLETON) {
      doSettermPropagation(x, S);
      if(d_conflict) return;
    }// propagation: children


    // propagation : parents
    Debug("sets-prop") << "[sets-prop] Propagating 'up' for "
                       << x << element_of_str << S << std::endl;
    const CDTNodeList* parentList = d_termInfoManager->getParents(S);
    for(typeof(parentList->begin()) k = parentList->begin();
        k != parentList->end(); ++k) {
      doSettermPropagation(x, *k);
      if(d_conflict) return;
    }// propagation : parents


  }//j loop

}/* TheorySetsPrivate::assertMemebership() */


void TheorySetsPrivate::doSettermPropagation(TNode x, TNode S)
{
  Debug("sets-prop") << "[sets-prop] doSettermPropagation("
                     << x << ", " << S << std::endl;

  Assert(S.getType().isSet() && S.getType().getSetElementType() == x.getType(),
         ( std::string("types of S and x are ") + S.getType().toString() +
           std::string(" and ") + x.getType().toString() +
           std::string(" respectively") ).c_str()  );

  Node literal, left_literal, right_literal;

  // axiom: literal <=> left_literal AND right_literal
  switch(S.getKind()) {
  case kind::INTERSECTION:
    literal       =       MEMBER(x, S)      ;
    left_literal  =       MEMBER(x, S[0])   ;
    right_literal =       MEMBER(x, S[1])   ;
    break;
  case kind::UNION:
    literal       = NOT(  MEMBER(x, S)     );
    left_literal  = NOT(  MEMBER(x, S[0])  );
    right_literal = NOT(  MEMBER(x, S[1])  );
    break;
  case kind::SETMINUS:
    literal       =       MEMBER(x, S)      ;
    left_literal  =       MEMBER(x, S[0])   ;
    right_literal = NOT(  MEMBER(x, S[1])  );
    break;
  case kind::SINGLETON: {
    Node atom = MEMBER(x, S);
    if(holds(atom, true)) {
      learnLiteral(EQUAL(x, S[0]), true, atom);
    } else if(holds(atom, false)) {
      learnLiteral(EQUAL(x, S[0]), false, NOT(atom));
    }
    return;
  }
  default:
    Unhandled();
  }

  Debug("sets-prop-details")
    << "[sets-prop-details]   " << literal << " IFF " << left_literal
    << " AND " << right_literal << std::endl;

  Debug("sets-prop-details")
    << "[sets-prop-details]   "
    << (holds(literal) ? "yes" : (holds(literal.negate()) ? " no" : " _ "))
    << " IFF "
    << (holds(left_literal) ? "yes" : (holds(left_literal.negate()) ? "no " : " _ "))
    << " AND "
    << (holds(right_literal) ? "yes" : (holds(right_literal.negate()) ? "no " : " _ "))
    << std::endl;

  Assert( present( MEMBER(x, S)    ) ||
          present( MEMBER(x, S[0]) ) ||
          present( MEMBER(x, S[1]) ) );

  if( holds(literal) ) {
    // 1a. literal => left_literal
    Debug("sets-prop") << "[sets-prop]  ... via case 1a. ..." << std::endl;
    learnLiteral(left_literal, literal);
    if(d_conflict) return;

    // 1b. literal => right_literal
    Debug("sets-prop") << "[sets-prop]  ... via case 1b. ..." << std::endl;
    learnLiteral(right_literal, literal);
    if(d_conflict) return;

    // subsumption requirement met, exit
    return;
  }
  else if( holds(literal.negate() ) ) {
    // 4. neg(literal), left_literal => neg(right_literal)
    if( holds(left_literal) ) {
      Debug("sets-prop") << "[sets-prop]  ... via case 4. ..." << std::endl;
      learnLiteral(right_literal.negate(), AND( literal.negate(),
                                                left_literal) );
      if(d_conflict) return;
    }

    // 5. neg(literal), right_literal => neg(left_literal)
    if( holds(right_literal) ) {
      Debug("sets-prop") << "[sets-prop]  ... via case 5. ..." << std::endl;
      learnLiteral(left_literal.negate(), AND( literal.negate(),
                                               right_literal) );
      if(d_conflict) return;
    }
  }
  else {
    // 2,3. neg(left_literal) v neg(right_literal) => neg(literal)
    if(holds(left_literal.negate())) {
      Debug("sets-prop") << "[sets-prop]  ... via case 2. ..." << std::endl;
      learnLiteral(literal.negate(), left_literal.negate());
      if(d_conflict) return;
    }
    else if(holds(right_literal.negate())) {
      Debug("sets-prop") << "[sets-prop]  ... via case 3. ..." << std::endl;
      learnLiteral(literal.negate(), right_literal.negate());
      if(d_conflict) return;
    }

    // 6. the axiom itself:
    else if(holds(left_literal) && holds(right_literal)) {
      Debug("sets-prop") << "[sets-prop]  ... via case 6. ..." << std::endl;
      learnLiteral(literal, AND(left_literal, right_literal) );
      if(d_conflict) return;
    }
  }

  // check fulfilling rule
  Node n;
  switch(S.getKind()) {
  case kind::UNION:
    if( holds(MEMBER(x, S)) &&
        !present( MEMBER(x, S[0]) ) )
      addToPending( MEMBER(x, S[0]) );
    break;
  case kind::SETMINUS: // intentional fallthrough
  case kind::INTERSECTION:
    if( holds(MEMBER(x, S[0])) &&
        !present( MEMBER(x, S[1]) ))
      addToPending( MEMBER(x, S[1]) );
    break;
  default:
    Assert(false, "MembershipEngine::doSettermPropagation");
  }
}


void TheorySetsPrivate::learnLiteral(TNode atom, bool polarity, Node reason) {
  Debug("sets-learn") << "[sets-learn] learnLiteral(" << atom
                      << ", " << polarity << ")" << std::endl;

  if( holds(atom, polarity) ) {
    Debug("sets-learn") << "[sets-learn] \u2514 already known, skipping" << std::endl;
    return;
  }

  if( holds(atom, !polarity) ) {
    Debug("sets-learn") << "[sets-learn] \u2514 conflict found" << std::endl;

    registerReason(reason, /*save=*/ true);

    if(atom.getKind() == kind::EQUAL) {
      d_equalityEngine.assertEquality(atom, polarity, reason);
    } else {
      d_equalityEngine.assertPredicate(atom, polarity, reason);
    }
    Assert(d_conflict);       // should be marked due to equality engine
    return;
  }

  Assert(atom.getKind() == kind::EQUAL || atom.getKind() == kind::MEMBER);

  Node learnt_literal = polarity ? Node(atom) : NOT(atom);
  d_propagationQueue.push_back( make_pair(learnt_literal, reason) );
}/*TheorySetsPrivate::learnLiteral(...)*/


/************************ Sharing ************************/
/************************ Sharing ************************/
/************************ Sharing ************************/

void TheorySetsPrivate::addSharedTerm(TNode n) {
  Debug("sets") << "[sets] ThoerySetsPrivate::addSharedTerm( " << n << ")" << std::endl;
  d_termInfoManager->addTerm(n);
  d_equalityEngine.addTriggerTerm(n, THEORY_SETS);
}

void TheorySetsPrivate::dumpAssertionsHumanified() const
{
    std::string tag = "sets-assertions";

    if(Trace.isOn(tag)) { /* condition can't be !Trace.isOn, that's why this empty block */ }
    else { return; }

    context::CDList<Assertion>::const_iterator it = d_external.facts_begin(), it_end = d_external.facts_end();

    std::map<TNode, std::set<TNode> > equalities;
    std::set< pair<TNode, TNode> > disequalities;
    std::map<TNode, std::pair<std::set<TNode>, std::set<TNode> > > members;
    static std::map<TNode, int> numbering;
    static int number = 0;

    for (unsigned i = 0; it != it_end; ++ it, ++i) {
      TNode ass = (*it).assertion;
      // Trace("sets-care-dump") << AssertCommand(ass.toExpr()) << endl;
      bool polarity = ass.getKind() != kind::NOT;
      ass = polarity ? ass : ass[0];
      Assert( ass.getNumChildren() == 2);
      TNode left = d_equalityEngine.getRepresentative(ass[0]);
      TNode right = d_equalityEngine.getRepresentative(ass[1]);
      if(numbering[left] == 0) numbering[left] = ++number;
      if(numbering[right] == 0) numbering[right] = ++number;
      equalities[left].insert(ass[0]);
      equalities[right].insert(ass[1]);
      if(ass.getKind() == kind::EQUAL) {
        if(polarity) {
          Assert(left == right);
        } else {
          if(left > right) std::swap(left, right);
          disequalities.insert(make_pair(left, right));
        }
      } else if(ass.getKind() == kind::MEMBER) {
        (polarity ? members[right].first : members[right].second).insert(left);
      }
    }
#define FORIT(it, container) for(typeof((container).begin()) it=(container).begin(); (it) != (container).end(); ++(it))
    FORIT(kt, equalities) {
      Trace(tag) << " Eq class of t" << numbering[(*kt).first] << ": " << std::endl;
      FORIT(jt, (*kt).second) {
        TNode S = (*jt);
        if( S.getKind() != kind::UNION && S.getKind() != kind::INTERSECTION && S.getKind() != kind::SETMINUS) {
          Trace(tag) << "    " << *jt << ((*jt).getType().isSet() ? "\n": " ");
        } else {
          Trace(tag) << "    ";
          if(S[0].isConst() || numbering.find(d_equalityEngine.getRepresentative(S[0])) == numbering.end()) {
            Trace(tag) << S[0];
          } else {
            Trace(tag) << "t" << numbering[d_equalityEngine.getRepresentative(S[0])];
          }
          Trace(tag) << " " << (S.getKind() == kind::UNION ? "|" : (S.getKind() == kind::INTERSECTION ? "&" : "-")) << " ";
          if(S[1].isConst() || numbering.find(d_equalityEngine.getRepresentative(S[1])) == numbering.end()) {
            Trace(tag) << S[1];
          } else {
            Trace(tag) << "t" << numbering[d_equalityEngine.getRepresentative(S[1])];
          }
          Trace(tag) << std::endl;
        }
      }
      Trace(tag) << std::endl;
    }
    FORIT(kt, disequalities) Trace(tag) << "NOT(t"<<numbering[(*kt).first]<<" = t" <<numbering[(*kt).second] <<")"<< std::endl;
    FORIT(kt, members) {
      if( (*kt).second.first.size() > 0) {
        Trace(tag) << "IN t" << numbering[(*kt).first] << ": ";
        FORIT(jt, (*kt).second.first) {
          TNode x = (*jt);
          if(x.isConst() || numbering.find(d_equalityEngine.getRepresentative(x)) == numbering.end()) {
            Trace(tag) << x << ", ";
          } else {
            Trace(tag) << "t" << numbering[d_equalityEngine.getRepresentative(x)] << ", ";
          }
        }
        Trace(tag) << std::endl;
      }
      if( (*kt).second.second.size() > 0) {
        Trace(tag) << "NOT IN t" << numbering[(*kt).first] << ": ";
        FORIT(jt, (*kt).second.second) {
          TNode x = (*jt);
          if(x.isConst() || numbering.find(d_equalityEngine.getRepresentative(x)) == numbering.end()) {
            Trace(tag) << x << ", ";
          } else {
            Trace(tag) << "t" << numbering[d_equalityEngine.getRepresentative(x)] << ", ";
          }
        }
        Trace(tag) << std::endl;
      }
    }
    Trace(tag) << std::endl;
#undef FORIT
}

void TheorySetsPrivate::computeCareGraph() {
  Debug("sharing") << "Theory::computeCareGraph<" << d_external.identify() << ">()" << endl;

  if(Trace.isOn("sets-assertions")) {
    // dump our understanding of assertions
    dumpAssertionsHumanified();
  }

  CVC4_UNUSED unsigned edgesAddedCnt = 0;

  unsigned i_st = 0;
  if(options::setsCare1()) { i_st = d_ccg_i; }
  for (unsigned i = i_st; i < d_external.d_sharedTerms.size(); ++ i) {
    TNode a = d_external.d_sharedTerms[i];
    TypeNode aType = a.getType();

    unsigned j_st = i + 1;
    if(options::setsCare1()) { if(i == d_ccg_i) j_st = d_ccg_j + 1; }

    for (unsigned j = j_st; j < d_external.d_sharedTerms.size(); ++ j) {
      TNode b = d_external.d_sharedTerms[j];
      if (b.getType() != aType) {
        // We don't care about the terms of different types
        continue;
      }

      switch (d_external.d_valuation.getEqualityStatus(a, b)) {
      case EQUALITY_TRUE_AND_PROPAGATED:
        // If we know about it, we should have propagated it, so we can skip
        Trace("sets-care") << "[sets-care] Know: " << EQUAL(a, b) << std::endl;
        break;
      case EQUALITY_FALSE_AND_PROPAGATED:
        // If we know about it, we should have propagated it, so we can skip
        Trace("sets-care") << "[sets-care] Know: " << NOT(EQUAL(a, b)) << std::endl;
        break;
      case EQUALITY_FALSE:
      case EQUALITY_TRUE:
        Assert(false, "ERROR: Equality status true/false but not propagated (sets care graph computation).");
        break;
      case EQUALITY_TRUE_IN_MODEL:
        d_external.addCarePair(a, b);
        if(Trace.isOn("sharing")) {
          ++edgesAddedCnt;
        }
        if(Debug.isOn("sets-care")) {
          Debug("sets-care") << "[sets-care] Requesting split between" << a << " and "
                << b << "." << std::endl << "[sets-care] "
                << "  Both current have value "
                << d_external.d_valuation.getModelValue(a) << std::endl;
        }
      case EQUALITY_FALSE_IN_MODEL:
        if(Trace.isOn("sets-care-performance-test")) {
          // TODO: delete these lines, only for performance testing for now
          d_external.addCarePair(a, b);
        }
        break;
      case EQUALITY_UNKNOWN:
        // Let's split on it
        d_external.addCarePair(a, b);
        if(options::setsCare1()) {
          d_ccg_i = i;
          d_ccg_j = j;
          return;
        }
        break;
      default:
        Unreachable();
      }
    }
  }
  Trace("sharing") << "TheorySetsPrivate::computeCareGraph(): size = " << edgesAddedCnt << std::endl;
}

EqualityStatus TheorySetsPrivate::getEqualityStatus(TNode a, TNode b) {
  Assert(d_equalityEngine.hasTerm(a) && d_equalityEngine.hasTerm(b));
  if (d_equalityEngine.areEqual(a, b)) {
    // The terms are implied to be equal
    return EQUALITY_TRUE;
  }
  if (d_equalityEngine.areDisequal(a, b, false)) {
    // The terms are implied to be dis-equal
    return EQUALITY_FALSE;
  }
  Node aModelValue = d_external.d_valuation.getModelValue(a);
  if(aModelValue.isNull()) { return EQUALITY_UNKNOWN; }
  Node bModelValue = d_external.d_valuation.getModelValue(b);
  if(bModelValue.isNull()) { return EQUALITY_UNKNOWN; }
  if( aModelValue == bModelValue ) {
    // The term are true in current model
    return EQUALITY_TRUE_IN_MODEL;
  } else {
    return EQUALITY_FALSE_IN_MODEL;
  }
  // }
  // //TODO: can we be more precise sometimes?
  // return EQUALITY_UNKNOWN;
}

/******************** Model generation ********************/
/******************** Model generation ********************/
/******************** Model generation ********************/

const TheorySetsPrivate::Elements& TheorySetsPrivate::getElements
(TNode setterm, SettermElementsMap& settermElementsMap) const {
  SettermElementsMap::const_iterator it = settermElementsMap.find(setterm);
  bool alreadyCalculated = (it != settermElementsMap.end());
  if( !alreadyCalculated ) {

    Kind k = setterm.getKind();
    Elements cur;

    switch(k) {
    case kind::UNION: {
      const Elements& left = getElements(setterm[0], settermElementsMap);
      const Elements& right = getElements(setterm[1], settermElementsMap);
      if(left.size() >= right.size()) {
        cur = left; cur.insert(right.begin(), right.end());
      } else {
        cur = right; cur.insert(left.begin(), left.end());
      }
      break;
    }
    case kind::INTERSECTION: {
      const Elements& left = getElements(setterm[0], settermElementsMap);
      const Elements& right = getElements(setterm[1], settermElementsMap);
      std::set_intersection(left.begin(), left.end(), right.begin(), right.end(),
                            std::inserter(cur, cur.begin()) );
      break;
    }
    case kind::SETMINUS: {
      const Elements& left = getElements(setterm[0], settermElementsMap);
      const Elements& right = getElements(setterm[1], settermElementsMap);
      std::set_difference(left.begin(), left.end(), right.begin(), right.end(),
                          std::inserter(cur, cur.begin()) );
      break;
    }
    default:
      Assert(theory::kindToTheoryId(k) != theory::THEORY_SETS,
             (std::string("Kind belonging to set theory not explicitly handled: ") + kindToString(k)).c_str());
      // Assert(k == kind::VARIABLE || k == kind::APPLY_UF || k == kind::SKOLEM,
      //        (std::string("Expect variable or UF got ") + kindToString(k)).c_str() );
      /* assign emptyset, which is default */
    }

    it = settermElementsMap.insert(SettermElementsMap::value_type(setterm, cur)).first;
  }
  return it->second;
}


bool TheorySetsPrivate::checkModel(const SettermElementsMap& settermElementsMap, TNode S) const {

  Debug("sets-model") << "[sets-model] checkModel(..., " << S << "): "
                      << std::endl;

  Assert(S.getType().isSet());

  const Elements emptySetOfElements;
  const Elements& saved =
    d_equalityEngine.getRepresentative(S).getKind() == kind::EMPTYSET ||
    settermElementsMap.find(d_equalityEngine.getRepresentative(S)) == settermElementsMap.end() ?
    emptySetOfElements :
    settermElementsMap.find(d_equalityEngine.getRepresentative(S))->second;
  Debug("sets-model") << "[sets-model] saved :  { ";
  BOOST_FOREACH(TNode element, saved) { Debug("sets-model") << element << ", "; }
  Debug("sets-model") << " }" << std::endl;

  if(theory::kindToTheoryId(S.getKind()) == THEORY_SETS && S.getNumChildren() == 2) {

    Elements cur;

    const Elements& left =
      d_equalityEngine.getRepresentative(S[0]).getKind() == kind::EMPTYSET ||
      settermElementsMap.find(d_equalityEngine.getRepresentative(S[0])) == settermElementsMap.end() ?
      emptySetOfElements :
      settermElementsMap.find(d_equalityEngine.getRepresentative(S[0]))->second;

    const Elements&  right =
      d_equalityEngine.getRepresentative(S[1]).getKind() == kind::EMPTYSET ||
      settermElementsMap.find(d_equalityEngine.getRepresentative(S[1])) == settermElementsMap.end() ?
      emptySetOfElements :
      settermElementsMap.find(d_equalityEngine.getRepresentative(S[1]))->second;

    switch(S.getKind()) {
    case kind::UNION:
      if(left.size() >= right.size()) {
        cur = left; cur.insert(right.begin(), right.end());
      } else {
        cur = right; cur.insert(left.begin(), left.end());
      }
      break;
    case kind::INTERSECTION:
      std::set_intersection(left.begin(), left.end(), right.begin(), right.end(),
                            std::inserter(cur, cur.begin()) );
      break;
    case kind::SETMINUS:
      std::set_difference(left.begin(), left.end(), right.begin(), right.end(),
                          std::inserter(cur, cur.begin()) );
      break;
    default:
      Unhandled();
    }

    Debug("sets-model") << "[sets-model] cur :  { ";
    BOOST_FOREACH(TNode element, cur) { Debug("sets-model") << element << ", "; }
    Debug("sets-model") << " }" << std::endl;

    if(saved != cur) {
      Debug("sets-model") << "[sets-model] *** ERROR *** cur != saved "
                          << std::endl;
      Debug("sets-model")
      << "[sets-model]   FYI: "
      << "  [" << S << "] = " << d_equalityEngine.getRepresentative(S) << ", "
      << "  [" << S[0] << "] = " << d_equalityEngine.getRepresentative(S[0]) << ", "
      << "  [" << S[1] << "] = " << d_equalityEngine.getRepresentative(S[1]) << "\n";

      return false;
    }
  }
  return true;
}

Node TheorySetsPrivate::elementsToShape(Elements elements, TypeNode setType) const
{
  NodeManager* nm = NodeManager::currentNM();

  if(elements.size() == 0) {
    return nm->mkConst<EmptySet>(EmptySet(nm->toType(setType)));
  } else {
    Elements::iterator it = elements.begin();
    Node cur = SINGLETON(*it);
    while( ++it != elements.end() ) {
      cur = nm->mkNode(kind::UNION, cur, SINGLETON(*it));
    }
    return cur;
  }
}
Node TheorySetsPrivate::elementsToShape(set<Node> elements, TypeNode setType) const
{
  NodeManager* nm = NodeManager::currentNM();

  if(elements.size() == 0) {
    return nm->mkConst<EmptySet>(EmptySet(nm->toType(setType)));
  } else {
    typeof(elements.begin()) it = elements.begin();
    Node cur = SINGLETON(*it);
    while( ++it != elements.end() ) {
      cur = nm->mkNode(kind::UNION, cur, SINGLETON(*it));
    }
    return cur;
  }
}

void TheorySetsPrivate::collectModelInfo(TheoryModel* m, bool fullModel)
{
  Debug("sets-model") << "[sets-model] collectModelInfo(..., fullModel="
                      << (fullModel ? "true)" : "false)") << std::endl;

  set<Node> terms;

  if(Trace.isOn("sets-assertions")) {
    dumpAssertionsHumanified();
  }

  // Compute terms appearing assertions and shared terms
  d_external.computeRelevantTerms(terms);

  // Compute for each setterm elements that it contains
  SettermElementsMap settermElementsMap;
  for(eq::EqClassIterator it_eqclasses(d_trueNode, &d_equalityEngine);
      ! it_eqclasses.isFinished() ; ++it_eqclasses) {
    TNode n = (*it_eqclasses);
    if(n.getKind() == kind::MEMBER) {
      Assert(d_equalityEngine.areEqual(n, d_trueNode));
      TNode x = d_equalityEngine.getRepresentative(n[0]);
      TNode S = d_equalityEngine.getRepresentative(n[1]);
      settermElementsMap[S].insert(x);
    }
    if(Debug.isOn("sets-model-details")) {
      vector<TNode> explanation;
      d_equalityEngine.explainPredicate(n, true, explanation);
      Debug("sets-model-details")
        << "[sets-model-details]  >  node: " << n << ", explanation:" << std::endl;
      BOOST_FOREACH(TNode m, explanation) {
        Debug("sets-model-details") << "[sets-model-details]  >>  " << m << std::endl;
      }
    }
  }

  if(Debug.isOn("sets-model-details")) {
    for(eq::EqClassIterator it_eqclasses(d_trueNode, &d_equalityEngine);
        ! it_eqclasses.isFinished() ; ++it_eqclasses) {
      TNode n = (*it_eqclasses);
      vector<TNode> explanation;
      d_equalityEngine.explainPredicate(n, false, explanation);
      Debug("sets-model-details")
        << "[sets-model-details]  >  node: not: " << n << ", explanation:" << std::endl;
      BOOST_FOREACH(TNode m, explanation) {
        Debug("sets-model-details") << "[sets-model-details]  >>  " << m << std::endl;
      }
    }
  }

  // Assert equalities and disequalities to the model
  m->assertEqualityEngine(&d_equalityEngine, &terms);

  // Loop over terms to collect set-terms for which we generate models
  set<Node> settermsModEq;
  BOOST_FOREACH(TNode term, terms) {
    TNode n = term.getKind() == kind::NOT ? term[0] : term;

    Debug("sets-model-details") << "[sets-model-details]  >   " << n << std::endl;

    if(n.getType().isSet()) {
      n = d_equalityEngine.getRepresentative(n);
      if( !n.isConst() ) {
        settermsModEq.insert(n);
      }
    }

  }

  if(Debug.isOn("sets-model")) {
    BOOST_FOREACH( TNode node, settermsModEq ) {
      Debug("sets-model") << "[sets-model]   " << node << std::endl;
    }
  }

  BOOST_FOREACH( SettermElementsMap::value_type &it, settermElementsMap ) {
    BOOST_FOREACH( TNode element, it.second /* elements */ ) {
      Debug("sets-model-details") << "[sets-model-details]  >   " <<
        (it.first /* setterm */) << ": " << element << std::endl;
    }
  }

  // assign representatives to equivalence class
  BOOST_FOREACH( TNode setterm, settermsModEq ) {
    Elements elements = getElements(setterm, settermElementsMap);
    Node shape = elementsToShape(elements, setterm.getType());
    shape = theory::Rewriter::rewrite(shape);
    m->assertEquality(shape, setterm, true);
    m->assertRepresentative(shape);
  }

#ifdef CVC4_ASSERTIONS
  bool checkPassed = true;
  BOOST_FOREACH(TNode term, terms) {
    if( term.getType().isSet() ) {
      checkPassed &= checkModel(settermElementsMap, term);
    }
  }
  if(Trace.isOn("sets-checkmodel-ignore")) {
    Trace("sets-checkmodel-ignore") << "[sets-checkmodel-ignore] checkPassed value was " << checkPassed << std::endl;
  } else {
    Assert( checkPassed,
            "THEORY_SETS check-model failed. Run with -d sets-model for details." );
  }
#endif
}

Node TheorySetsPrivate::getModelValue(TNode n)
{
  CodeTimer codeTimer(d_statistics.d_getModelValueTime);
  return d_termInfoManager->getModelValue(n);
}

/********************** Helper functions ***************************/
/********************** Helper functions ***************************/
/********************** Helper functions ***************************/

Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;

  for (unsigned i = 0; i < conjunctions.size(); ++i) {
    TNode t = conjunctions[i];

    if (t.getKind() == kind::AND) {
      for(TNode::iterator child_it = t.begin();
          child_it != t.end(); ++child_it) {
        Assert((*child_it).getKind() != kind::AND);
        all.insert(*child_it);
      }
    }
    else {
      all.insert(t);
    }

  }

  Assert(all.size() > 0);

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}/* mkAnd() */


TheorySetsPrivate::Statistics::Statistics() :
    d_getModelValueTime("theory::sets::getModelValueTime")
  , d_memberLemmas("theory::sets::lemmas::member", 0)
  , d_disequalityLemmas("theory::sets::lemmas::disequality", 0)
{
  StatisticsRegistry::registerStat(&d_getModelValueTime);
  StatisticsRegistry::registerStat(&d_memberLemmas);
  StatisticsRegistry::registerStat(&d_disequalityLemmas);
}


TheorySetsPrivate::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_getModelValueTime);
  StatisticsRegistry::unregisterStat(&d_memberLemmas);
  StatisticsRegistry::unregisterStat(&d_disequalityLemmas);
}


bool TheorySetsPrivate::present(TNode atom) {
  return holds(atom) || holds(atom.notNode());
}


bool TheorySetsPrivate::holds(TNode atom, bool polarity) {
  TNode polarity_atom = polarity ? d_trueNode : d_falseNode;

  Node atomModEq = NodeManager::currentNM()->mkNode
    (atom.getKind(), d_equalityEngine.getRepresentative(atom[0]),
     d_equalityEngine.getRepresentative(atom[1]) );

  d_equalityEngine.addTerm(atomModEq);

  return d_equalityEngine.areEqual(atomModEq, polarity_atom);
}


void TheorySetsPrivate::registerReason(TNode reason, bool save)
{
  if(save) d_nodeSaver.insert(reason);

  if(reason.getKind() == kind::AND) {
    Assert(reason.getNumChildren() == 2);
    registerReason(reason[0], false);
    registerReason(reason[1], false);
  } else if(reason.getKind() == kind::NOT) {
    registerReason(reason[0], false);
  } else if(reason.getKind() == kind::MEMBER) {
    d_equalityEngine.addTerm(reason);
    Assert(present(reason));
  } else if(reason.getKind() == kind::EQUAL) {
    d_equalityEngine.addTerm(reason);
    Assert(present(reason));
  } else if(reason.getKind() == kind::CONST_BOOLEAN) {
    // That's OK, already in EqEngine
  } else {
    Unhandled();
  }
}

void TheorySetsPrivate::finishPropagation()
{
  while(!d_conflict && !d_settermPropagationQueue.empty()) {
    std::pair<TNode,TNode> np = d_settermPropagationQueue.front();
    d_settermPropagationQueue.pop();
    doSettermPropagation(np.first, np.second);
  }
  while(!d_conflict && !d_propagationQueue.empty()) {
    std::pair<Node,Node> np = d_propagationQueue.front();
    d_propagationQueue.pop();
    TNode atom = np.first.getKind() == kind::NOT ? np.first[0] : np.first;
    if(atom.getKind() == kind::MEMBER) {
      assertMemebership(np.first, np.second, /* learnt = */ true);
    } else {
      assertEquality(np.first, np.second, /* learnt = */ true);
    }
  }
}

void TheorySetsPrivate::addToPending(Node n) {
  Debug("sets-pending") << "[sets-pending] addToPending " << n << std::endl;

  if(d_pendingEverInserted.find(n) != d_pendingEverInserted.end()) {
    Debug("sets-pending") << "[sets-pending] \u2514 skipping " << n
        << " as lemma already generated." << std::endl;
    return;
  }

  if(n.getKind() == kind::MEMBER) {

    Node nRewritten = theory::Rewriter::rewrite(n);

    if(nRewritten.isConst()) {
      Debug("sets-pending") << "[sets-pending] \u2514 skipping " << n
          << " as we can learn one of the sides." << std::endl;
      Assert(nRewritten == d_trueNode || nRewritten == d_falseNode);

      bool polarity = (nRewritten == d_trueNode);
      learnLiteral(n, polarity, d_trueNode);
      return;
    }

    Debug("sets-pending") << "[sets-pending] \u2514 added to member queue"
        << std::endl;
    ++d_statistics.d_memberLemmas;
    d_pending.push(n);
    d_external.d_out->splitLemma(getLemma());
    Assert(isComplete());

  } else {

    Debug("sets-pending") << "[sets-pending] \u2514 added to equality queue"
        << std::endl;
    Assert(n.getKind() == kind::EQUAL);
    ++d_statistics.d_disequalityLemmas;
    d_pendingDisequal.push(n);
    d_external.d_out->splitLemma(getLemma());
    Assert(isComplete());

  }
}

bool TheorySetsPrivate::isComplete() {
  // while(!d_pending.empty() &&
  //       (d_pendingEverInserted.find(d_pending.front()) != d_pendingEverInserted.end()
  //        || present(d_pending.front()) ) ) {
  //   Debug("sets-pending") << "[sets-pending] removing as already present: "
  //                         << d_pending.front() << std::endl;
  //   d_pending.pop();
  // }
  return d_pending.empty() && d_pendingDisequal.empty();
}

Node TheorySetsPrivate::getLemma() {
  Assert(!d_pending.empty() || !d_pendingDisequal.empty());

  Node n, lemma;

  if(!d_pending.empty()) {
    n = d_pending.front();
    d_pending.pop();
    d_pendingEverInserted.insert(n);

    Assert(!present(n));
    Assert(n.getKind() == kind::MEMBER);

    lemma = OR(n, NOT(n));
  } else {
    n = d_pendingDisequal.front();
    d_pendingDisequal.pop();
    d_pendingEverInserted.insert(n);

    Assert(n.getKind() == kind::EQUAL && n[0].getType().isSet());
    TypeNode elementType = n[0].getType().getSetElementType();
    Node x = NodeManager::currentNM()->mkSkolem("sde_",  elementType);
    Node l1 = MEMBER(x, n[0]), l2 = MEMBER(x, n[1]);

    lemma = OR(n, AND(l1, NOT(l2)), AND(NOT(l1), l2));
  }

  Debug("sets-lemma") << "[sets-lemma] Generating for " << n
                      << ", lemma: " << lemma << std::endl;

  return  lemma;
}


TheorySetsPrivate::TheorySetsPrivate(TheorySets& external,
                                     context::Context* c,
                                     context::UserContext* u):
  d_external(external),
  d_notify(*this),
  d_equalityEngine(d_notify, c, "theory::sets::TheorySetsPrivate", true),
  d_trueNode(NodeManager::currentNM()->mkConst<bool>(true)),
  d_falseNode(NodeManager::currentNM()->mkConst<bool>(false)),
  d_conflict(c),
  d_termInfoManager(NULL),
  d_propagationQueue(c),
  d_settermPropagationQueue(c),
  d_nodeSaver(c),
  d_pending(c),
  d_pendingDisequal(c),
  d_pendingEverInserted(u),
  d_modelCache(c),
  d_ccg_i(c),
  d_ccg_j(c),
  d_scrutinize(NULL)
{
  d_termInfoManager = new TermInfoManager(*this, c, &d_equalityEngine);

  d_equalityEngine.addFunctionKind(kind::UNION);
  d_equalityEngine.addFunctionKind(kind::INTERSECTION);
  d_equalityEngine.addFunctionKind(kind::SETMINUS);

  d_equalityEngine.addFunctionKind(kind::MEMBER);
  d_equalityEngine.addFunctionKind(kind::SUBSET);

  if( Debug.isOn("sets-scrutinize") ) {
    d_scrutinize = new TheorySetsScrutinize(this);
  }
}/* TheorySetsPrivate::TheorySetsPrivate() */


TheorySetsPrivate::~TheorySetsPrivate()
{
  delete d_termInfoManager;
  if( Debug.isOn("sets-scrutinize") ) {
    Assert(d_scrutinize != NULL);
    delete d_scrutinize;
  }
}/* TheorySetsPrivate::~TheorySetsPrivate() */

void TheorySetsPrivate::propagate(Theory::Effort effort) {
  if(effort != Theory::EFFORT_FULL || !options::setsPropFull()) {
    return;
  }

  // build a model
  Trace("sets-prop-full") << "[sets-prop-full] propagate(FULL_EFFORT)" << std::endl;
  if(Trace.isOn("sets-assertions")) {
    dumpAssertionsHumanified();
  }

  const CDNodeSet& terms = (d_termInfoManager->d_terms);
  for(typeof(terms.key_begin()) it = terms.key_begin(); it != terms.key_end(); ++it) {
    Node node = (*it);
    Kind k = node.getKind();
    if(k == kind::UNION && node[0].getKind() == kind::SINGLETON ) {

      if(holds(MEMBER(node[0][0], node[1]))) {
        Trace("sets-prop-full") << "[sets-prop-full] " << MEMBER(node[0][0], node[1])
                                << " => " << EQUAL(node[1], node) << std::endl;
        learnLiteral(EQUAL(node[1], node), MEMBER(node[0][0], node[1]));
      }

    } else if(k == kind::UNION && node[1].getKind() == kind::SINGLETON ) {

      if(holds(MEMBER(node[1][0], node[0]))) {
        Trace("sets-prop-full") << "[sets-prop-full] " << MEMBER(node[1][0], node[0])
                                << " => " << EQUAL(node[0], node) << std::endl;
        learnLiteral(EQUAL(node[0], node), MEMBER(node[1][0], node[0]));
      }

    }
  }

  finishPropagation();
}

bool TheorySetsPrivate::propagate(TNode literal) {
  Debug("sets-prop") << " propagate(" << literal  << ")" << std::endl;

  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("sets-prop") << "TheoryUF::propagate(" << literal << "): already in conflict" << std::endl;
    return false;
  }

  // Propagate out
  bool ok = d_external.d_out->propagate(literal);
  if (!ok) {
    d_conflict = true;
  }

  return ok;
}/* TheorySetsPrivate::propagate(TNode) */


void TheorySetsPrivate::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}


void TheorySetsPrivate::conflict(TNode a, TNode b)
{
  if (a.getKind() == kind::CONST_BOOLEAN) {
    d_conflictNode = explain(a.iffNode(b));
  } else {
    d_conflictNode = explain(a.eqNode(b));
  }
  d_external.d_out->conflict(d_conflictNode);
  Debug("sets") << "[sets] conflict: " << a << " iff " << b
                << ", explaination " << d_conflictNode << std::endl;
  d_conflict = true;
}

Node TheorySetsPrivate::explain(TNode literal)
{
  Debug("sets") << "TheorySetsPrivate::explain(" << literal << ")"
                << std::endl;

  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  std::vector<TNode> assumptions;

  if(atom.getKind() == kind::EQUAL || atom.getKind() == kind::IFF) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else if(atom.getKind() == kind::MEMBER) {
    if( !d_equalityEngine.hasTerm(atom)) {
      d_equalityEngine.addTerm(atom);
    }
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  } else {
    Debug("sets") << "unhandled: " << literal << "; (" << atom << ", "
                  << polarity << "); kind" << atom.getKind() << std::endl;
    Unhandled();
  }

  return mkAnd(assumptions);
}


void TheorySetsPrivate::preRegisterTerm(TNode node)
{
  Debug("sets") << "TheorySetsPrivate::preRegisterTerm(" << node << ")"
                << std::endl;

  switch(node.getKind()) {
  case kind::EQUAL:
    // TODO: what's the point of this
    d_equalityEngine.addTriggerEquality(node);
    break;
  case kind::MEMBER:
    // TODO: what's the point of this
    d_equalityEngine.addTriggerPredicate(node);
    break;
  default:
    d_termInfoManager->addTerm(node);
    d_equalityEngine.addTriggerTerm(node, THEORY_SETS);
  }

  if(node.getKind() == kind::SINGLETON) {
    learnLiteral(MEMBER(node[0], node), true, d_trueNode);
  }
}



/**************************** eq::NotifyClass *****************************/
/**************************** eq::NotifyClass *****************************/
/**************************** eq::NotifyClass *****************************/


bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerEquality(TNode equality, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerEquality: equality = " << equality
                   << " value = " << value << std::endl;
  if (value) {
    return d_theory.propagate(equality);
  } else {
    // We use only literal triggers so taking not is safe
    return d_theory.propagate(equality.notNode());
  }
}

bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerPredicate(TNode predicate, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerPredicate: predicate = " << predicate
                   << " value = " << value << std::endl;
  if (value) {
    return d_theory.propagate(predicate);
  } else {
    return d_theory.propagate(predicate.notNode());
  }
}

bool TheorySetsPrivate::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyTriggerTermEquality: tag = " << tag
                   << " t1 = " << t1 << "  t2 = " << t2 << "  value = " << value << std::endl;
  if(value) {
    d_theory.d_termInfoManager->mergeTerms(t1, t2);
  }
  d_theory.propagate( value ? EQUAL(t1, t2) : NOT(EQUAL(t1, t2)) );
  return true;
}

void TheorySetsPrivate::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2)
{
  Debug("sets-eq") << "[sets-eq] eqNotifyConstantTermMerge " << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.conflict(t1, t2);
}

// void TheorySetsPrivate::NotifyClass::eqNotifyNewClass(TNode t)
// {
//   Debug("sets-eq") << "[sets-eq] eqNotifyNewClass:" << " t = " << t << std::endl;
// }

// void TheorySetsPrivate::NotifyClass::eqNotifyPreMerge(TNode t1, TNode t2)
// {
//   Debug("sets-eq") << "[sets-eq] eqNotifyPreMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
// }

// void TheorySetsPrivate::NotifyClass::eqNotifyPostMerge(TNode t1, TNode t2)
// {
//   Debug("sets-eq") << "[sets-eq] eqNotifyPostMerge:" << " t1 = " << t1 << " t2 = " << t2 << std::endl;
// }

// void TheorySetsPrivate::NotifyClass::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
// {
//   Debug("sets-eq") << "[sets-eq] eqNotifyDisequal:" << " t1 = " << t1 << " t2 = " << t2 << " reason = " << reason << std::endl;
// }


/**************************** TermInfoManager *****************************/
/**************************** TermInfoManager *****************************/
/**************************** TermInfoManager *****************************/

void TheorySetsPrivate::TermInfoManager::mergeLists
(CDTNodeList* la, const CDTNodeList* lb) const {
  // straight from theory/arrays/array_info.cpp
  std::set<TNode> temp;
  CDTNodeList::const_iterator it;
  for(it = la->begin() ; it != la->end(); it++ ) {
    temp.insert((*it));
  }

  for(it = lb->begin() ; it!= lb->end(); it++ ) {
    if(temp.count(*it) == 0) {
      la->push_back(*it);
    }
  }
}

TheorySetsPrivate::TermInfoManager::TermInfoManager
(TheorySetsPrivate& theory, context::Context* satContext, eq::EqualityEngine* eq):
  d_theory(theory),
  d_context(satContext),
  d_eqEngine(eq),
  d_terms(satContext),
  d_info()
{ }

TheorySetsPrivate::TermInfoManager::~TermInfoManager() {
  for( typeof(d_info.begin()) it = d_info.begin();
       it != d_info.end(); ++it) {
    delete (*it).second;
  }
}

void TheorySetsPrivate::TermInfoManager::notifyMembership(TNode fact) {
  bool polarity = fact.getKind() != kind::NOT;
  TNode atom = polarity ? fact : fact[0];

  TNode x = d_eqEngine->getRepresentative(atom[0]);
  TNode S = d_eqEngine->getRepresentative(atom[1]);

  Debug("sets-terminfo") << "[sets-terminfo] Adding membership " << x
                         << " in " << S << " " << polarity << std::endl;

  d_info[S]->addToElementList(x, polarity);
  d_info[x]->addToSetList(S, polarity);

  d_theory.d_modelCache.clear();
}

const CDTNodeList* TheorySetsPrivate::TermInfoManager::getParents(TNode x) {
  return d_info[x]->parents;
}

const CDTNodeList* TheorySetsPrivate::TermInfoManager::getMembers(TNode S) {
  return d_info[S]->elementsInThisSet;
}

const CDTNodeList* TheorySetsPrivate::TermInfoManager::getNonMembers(TNode S) {
  return d_info[S]->elementsNotInThisSet;
}

void TheorySetsPrivate::TermInfoManager::addTerm(TNode n) {
  if(d_terms.contains(n)) {
    return;
  }
  d_terms.insert(n);

  if(d_info.find(n) == d_info.end()) {
    d_info.insert(make_pair(n, new TheorySetsTermInfo(d_context)));
  }

  if(n.getKind() == kind::UNION ||
     n.getKind() == kind::INTERSECTION ||
     n.getKind() == kind::SETMINUS) {

    unsigned numChild = n.getNumChildren();

    for(unsigned i = 0; i < numChild; ++i) {
      Assert(d_terms.contains(n[i]));
      if(d_terms.contains(n[i])) {
        Debug("sets-parent") << "Adding " << n << " to parent list of "
                             << n[i] << std::endl;
        d_info[n[i]]->parents->push_back(n);

        typeof(d_info.begin()) ita = d_info.find(d_eqEngine->getRepresentative(n[i]));
        Assert(ita != d_info.end());
        CDTNodeList* l = (*ita).second->elementsNotInThisSet;
        for(typeof(l->begin()) it = l->begin(); it != l->end(); ++it) {
          d_theory.d_settermPropagationQueue.push_back( std::make_pair( (*it), n ) );
        }
        l = (*ita).second->elementsInThisSet;
        for(typeof(l->begin()) it = l->begin(); it != l->end(); ++it) {
          d_theory.d_settermPropagationQueue.push_back( std::make_pair( (*it), n ) );
        }
      }
    }
  }
}

void TheorySetsPrivate::TermInfoManager::pushToSettermPropagationQueue
(TNode x, TNode S, bool polarity)
{
  Node cur_atom = MEMBER(x, S);

  // propagation : empty set
  if(polarity && S.getKind() == kind::EMPTYSET) {
    Debug("sets-prop") << "[sets-prop]  something in empty set? conflict."
                       << std::endl;
    d_theory.learnLiteral(cur_atom, false, cur_atom);
    return;
  }// propagation: empty set

  // propagation : children
  if(S.getKind() == kind::UNION ||
     S.getKind() == kind::INTERSECTION ||
     S.getKind() == kind::SETMINUS ||
     S.getKind() == kind::SINGLETON) {
    d_theory.d_settermPropagationQueue.push_back(std::make_pair(x, S));
  }// propagation: children

  // propagation : parents
  const CDTNodeList* parentList = getParents(S);
  for(typeof(parentList->begin()) k = parentList->begin();
      k != parentList->end(); ++k) {
    d_theory.d_settermPropagationQueue.push_back(std::make_pair(x, *k));
  }// propagation : parents

}

void TheorySetsPrivate::TermInfoManager::pushToSettermPropagationQueue
(TNode x, CDTNodeList* l, bool polarity)
{
  set<TNode> alreadyProcessed;

  BOOST_FOREACH(TNode S, (*l) ) {
    Debug("sets-prop") << "[sets-terminfo]  setterm todo: "
                       << MEMBER(x, d_eqEngine->getRepresentative(S))
                       << std::endl;

    TNode repS = d_eqEngine->getRepresentative(S);
    if(alreadyProcessed.find(repS) != alreadyProcessed.end()) {
      continue;
    } else {
      alreadyProcessed.insert(repS);
    }

    d_eqEngine->addTerm(MEMBER(d_eqEngine->getRepresentative(x), repS));

    for(eq::EqClassIterator j(d_eqEngine->getRepresentative(S), d_eqEngine);
        !j.isFinished(); ++j) {

      pushToSettermPropagationQueue(x, *j, polarity);

    }//j loop
  }
}

void TheorySetsPrivate::TermInfoManager::pushToSettermPropagationQueue
(CDTNodeList* l, TNode S, bool polarity)
{
  BOOST_FOREACH(TNode x, (*l) ) {
    Debug("sets-prop") << "[sets-terminfo]  setterm todo: "
                       << MEMBER(x, d_eqEngine->getRepresentative(S))
                       << std::endl;

    d_eqEngine->addTerm(MEMBER(d_eqEngine->getRepresentative(x),
             d_eqEngine->getRepresentative(S)));

    for(eq::EqClassIterator j(d_eqEngine->getRepresentative(S), d_eqEngine);
        !j.isFinished(); ++j) {

      pushToSettermPropagationQueue(x, *j, polarity);

    }//j loop

  }

}



void TheorySetsPrivate::TermInfoManager::mergeTerms(TNode a, TNode b) {
  // merge b into a
  Debug("sets-terminfo") << "[sets-terminfo] Merging (into) a = " << a
                         << ", b = " << b << std::endl;
  Debug("sets-terminfo") << "[sets-terminfo] reps"
                         << ", a: " << d_eqEngine->getRepresentative(a)
                         << ", b: " << d_eqEngine->getRepresentative(b)
                         << std::endl;

  typeof(d_info.begin()) ita = d_info.find(a);
  typeof(d_info.begin()) itb = d_info.find(b);

  Assert(ita != d_info.end());
  Assert(itb != d_info.end());

  /* elements in this sets */
  pushToSettermPropagationQueue( (*ita).second->elementsInThisSet, b, true );
  pushToSettermPropagationQueue( (*ita).second->elementsNotInThisSet, b, false );
  pushToSettermPropagationQueue( (*itb).second->elementsNotInThisSet, a, false );
  pushToSettermPropagationQueue( (*itb).second->elementsInThisSet, a, true );
  mergeLists((*ita).second->elementsInThisSet,
             (*itb).second->elementsInThisSet);
  mergeLists((*ita).second->elementsNotInThisSet,
             (*itb).second->elementsNotInThisSet);

  /* sets containing this element */
  // pushToSettermPropagationQueue( b, (*ita).second->setsContainingThisElement, true);
  // pushToSettermPropagationQueue( b, (*ita).second->setsNotContainingThisElement, false);
  pushToSettermPropagationQueue( a, (*itb).second->setsNotContainingThisElement, false);
  pushToSettermPropagationQueue( a, (*itb).second->setsContainingThisElement, true);
  mergeLists( (*ita).second->setsContainingThisElement,
              (*itb).second->setsContainingThisElement );
  mergeLists( (*ita).second->setsNotContainingThisElement,
              (*itb).second->setsNotContainingThisElement );

  d_theory.d_modelCache.clear();
}

Node TheorySetsPrivate::TermInfoManager::getModelValue(TNode n)
{
  if(d_terms.find(n) == d_terms.end()) {
    return Node();
  }
  Assert(n.getType().isSet());
  set<Node> elements, elements_const;
  Node S = d_eqEngine->getRepresentative(n);
  typeof(d_theory.d_modelCache.begin()) it = d_theory.d_modelCache.find(S);
  if(it != d_theory.d_modelCache.end()) {
    return (*it).second;
  }
  const CDTNodeList* l = getMembers(S);
  for(typeof(l->begin()) it = l->begin(); it != l->end(); ++it) {
    TNode n = *it;
    elements.insert(d_eqEngine->getRepresentative(n));
  }
  BOOST_FOREACH(TNode e, elements) {
    if(e.isConst()) {
      elements_const.insert(e);
    } else {
      Node eModelValue = d_theory.d_external.d_valuation.getModelValue(e);
      if( eModelValue.isNull() ) return eModelValue;
      elements_const.insert(eModelValue);
    }
  }
  Node v = d_theory.elementsToShape(elements_const, n.getType());
  d_theory.d_modelCache[n] = v;
  return v;
}

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
