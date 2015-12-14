/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Clark Barrett
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An enumerator for sep
 **
 ** An enumerator for sep.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SEP__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__SEP__TYPE_ENUMERATOR_H

#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace sep {

class RefEnumerator : public TypeEnumeratorBase<RefEnumerator> {
  NodeManager* d_nm;
  //TypeEnumerator d_val;
  TypeNode d_constituentType;
  bool d_finished;
  Integer d_count;
public:

  RefEnumerator(TypeNode type) throw(AssertionException) :
    TypeEnumeratorBase<RefEnumerator>(type),
    d_nm(NodeManager::currentNM()),
    //d_val(type.getRefConstituentType()),
    d_constituentType(type.getRefConstituentType()),
    d_finished(false), 
    d_count(0){
  }
  RefEnumerator(const RefEnumerator& ae) throw() :
    TypeEnumeratorBase<RefEnumerator>(ae.d_nm->mkRefType(ae.d_constituentType)),
    d_nm(ae.d_nm),
    //d_val(ae.d_val),
    d_constituentType(ae.d_constituentType),
    d_finished(ae.d_finished), 
    d_count(ae.d_count){
  }

  ~RefEnumerator() {}

  Node operator*() throw(NoMoreValuesException) {
    if (d_finished) {
      throw NoMoreValuesException(getType());
    }
    //TODO : convert to ref
    //Node n = *d_val;
    //Trace("sep-type-enum") << "operator * prerewrite: " << n << std::endl;
    //n = Rewriter::rewrite(n);
    Trace("sep-type-enum") << "SepEnum: operator * returning uc: " << d_count << " " << getType() << std::endl;
    return NodeManager::currentNM()->mkConst(UninterpretedConstant(getType().toType(), d_count));
  }

  RefEnumerator& operator++() throw() {
    Trace("sep-type-enum") << "SepEnum: operator++ called, **this = " << **this << std::endl;

    if (d_finished) {
      Trace("sep-type-enum") << "SepEnum: operator++ already finished!" << std::endl;
      return *this;
    }
    /*
    //enumerate the constituent type (for cardinality purposes only)
    ++d_val;
    if (d_val.isFinished()) {
      Trace("sep-type-enum") << "SepEnum: operator++ finished!" << std::endl;
      d_finished = true;
    }else{
    */
    d_count += 1;
    return *this;
  }

  bool isFinished() throw() {
    Trace("sep-type-enum") << "SepEnum: isFinished returning: " << d_finished << std::endl;
    return d_finished;
  }

};/* class RefEnumerator */

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SEP__TYPE_ENUMERATOR_H */
