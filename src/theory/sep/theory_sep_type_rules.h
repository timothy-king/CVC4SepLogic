/*********************                                                        */
/*! \file theory_sep_type_rules.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Typing and cardinality rules for the theory of sep
 **
 ** Typing and cardinality rules for the theory of sep.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SEP__THEORY_SEP_TYPE_RULES_H
#define __CVC4__THEORY__SEP__THEORY_SEP_TYPE_RULES_H

#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace sep {

class NilRefTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    return TypeNode::fromType( n.getConst<NilRef>().getType() );
  }
};
  
class EmpStarTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    return nodeManager->booleanType();
  }  
};
  
struct SepPtoTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    Assert(n.getKind() == kind::SEP_PTO);
    if( check ) {
      TypeNode refType = n[0].getType(check);
      if(!refType.isRef()) {
        throw TypeCheckingExceptionPrivate(n, "pto applied to non-reference term");
      }
      TypeNode ptType = n[1].getType(check);
      if(!ptType.isComparableTo(refType.getRefConstituentType())){
        throw TypeCheckingExceptionPrivate(n, "pto maps reference to term of different type");
      }
    }
    return nodeManager->booleanType();
  }
};/* struct SepSelectTypeRule */

struct SepStarTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    TypeNode btype = nodeManager->booleanType();
    Assert(n.getKind() == kind::SEP_STAR);
    if( check ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        TypeNode ctype = n[i].getType( check );
        if( ctype!=btype ){
          throw TypeCheckingExceptionPrivate(n, "child of sep star is not Boolean");
        }
      }
    }
    return btype;
  }
};/* struct SepStarTypeRule */


class EmpStarInternalTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    return nodeManager->booleanType();
  }
};/* struct EmpStarInternalTypeRule */

struct SepLabelTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    TypeNode btype = nodeManager->booleanType();
    Assert(n.getKind() == kind::SEP_LABEL);
    if( check ){
      TypeNode ctype = n[0].getType( check );
      if( ctype!=btype ){
        throw TypeCheckingExceptionPrivate(n, "child of sep label is not Boolean");
      }
      TypeNode stype = n[1].getType( check );
      if( !stype.isSet() ){
        throw TypeCheckingExceptionPrivate(n, "label of sep label is not a set");
      }
    }
    return btype;
  }
};/* struct SepLabelTypeRule */

struct SepProperties {
  inline static Cardinality computeCardinality(TypeNode type) {
    Assert(type.getKind() == kind::REF_TYPE);
    Cardinality indexCard = type[0].getCardinality();
    return indexCard;
  }

  inline static bool isWellFounded(TypeNode type) {
    Assert(type.getKind() == kind::REF_TYPE);
    return type[0].isWellFounded();
  }

  inline static Node mkGroundTerm(TypeNode type) {
    return *TypeEnumerator(type);
  }
};/* struct SepProperties */

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SEP__THEORY_SEP_TYPE_RULES_H */
