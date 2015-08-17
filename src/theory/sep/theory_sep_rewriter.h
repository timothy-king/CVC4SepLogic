/*********************                                                        */
/*! \file theory_sep_rewriter.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SEP__THEORY_SEP_REWRITER_H
#define __CVC4__THEORY__SEP__THEORY_SEP_REWRITER_H

#include "theory/rewriter.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace sep {


class TheorySepRewriter {
public:

  static RewriteResponse postRewrite(TNode node) {
    Trace("sep-postrewrite") << "Sep::postRewrite start " << node << std::endl;
    switch (node.getKind()) {
      case kind::SEP_PTO: {
        
        break;
      }
      case kind::SEP_STAR: {
        
        break;
      }
      case kind::EQUAL:
      case kind::IFF: {
        if(node[0] == node[1]) {
          Trace("sep-postrewrite") << "Sep::postRewrite returning true" << std::endl;
          return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
        }
        else if (node[0].isConst() && node[1].isConst()) {
          Trace("sep-postrewrite") << "Sep::postRewrite returning false" << std::endl;
          return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
        }
        if (node[0] > node[1]) {
          Node newNode = NodeManager::currentNM()->mkNode(node.getKind(), node[1], node[0]);
          Trace("sep-postrewrite") << "Sep::postRewrite returning " << newNode << std::endl;
          return RewriteResponse(REWRITE_DONE, newNode);
        }
        break;
      }
      default:
        break;
    }
    Trace("sep-postrewrite") << "Sep::postRewrite returning " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline RewriteResponse preRewrite(TNode node) {

    Trace("sep-prerewrite") << "Sep::preRewrite returning " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline void init() {}
  static inline void shutdown() {}

};/* class TheorySepRewriter */

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SEP__THEORY_SEP_REWRITER_H */
