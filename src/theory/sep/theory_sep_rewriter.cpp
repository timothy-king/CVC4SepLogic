/*********************                                                        */
/*! \file theory_sep_rewriter.cpp
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

#include "expr/attribute.h"
#include "theory/sep/theory_sep_rewriter.h"

namespace CVC4 {
namespace theory {
namespace sep {
  
void TheorySepRewriter::getStarChildren( Node n, std::vector< Node >& children, std::vector< Node >& s_children, std::vector< Node >& ns_children ){
  if( n.getKind()==kind::SEP_STAR || n.getKind()==kind::AND ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      getStarChildren( n[i], children, s_children, ns_children );
    }
  }else{
    if( std::find( children.begin(), children.end(), n )==children.end() ){
      children.push_back( n );
      std::map< Node, bool > visited;
      if( isSpatial( n, visited ) ){
        s_children.push_back( n );
      }else{
        ns_children.push_back( n );
      }
    }
  }
}

bool TheorySepRewriter::isSpatial( Node n, std::map< Node, bool >& visited ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==kind::SEP_STAR || n.getKind()==kind::SEP_PTO || n.getKind()==kind::SEP_LABEL ){
      return true;
    }else if( n.getType().isBoolean() ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( isSpatial( n[i], visited ) ){
          return true;
        }
      }
    }
  }
  return false;
}
  
RewriteResponse TheorySepRewriter::postRewrite(TNode node) {
  Trace("sep-postrewrite") << "Sep::postRewrite start " << node << std::endl;
  Node retNode = node;
  switch (node.getKind()) {
    case kind::SEP_PTO: {
      break;
    }
    case kind::SEP_STAR: {
      //flatten
      std::vector< Node > children;
      std::vector< Node > s_children;
      std::vector< Node > ns_children;
      getStarChildren( node, children, s_children, ns_children );
      Node schild;
      if( s_children.size()==0 ){
        schild = NodeManager::currentNM()->mkConst( EmpStar() );
      }else if( s_children.size()==1) {
        schild = s_children[0];
      }else{
        schild = NodeManager::currentNM()->mkNode( kind::SEP_STAR, s_children );
      }
      ns_children.push_back( schild );
      if( ns_children.size()==1 ){
        retNode = ns_children[0];
      }else{
        retNode = NodeManager::currentNM()->mkNode( kind::AND, ns_children );
      }
      break;
    }
    case kind::EQUAL:
    case kind::IFF: {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      }
      else if (node[0].isConst() && node[1].isConst()) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
      }
      if (node[0] > node[1]) {
        Node newNode = NodeManager::currentNM()->mkNode(node.getKind(), node[1], node[0]);
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      break;
    }
    default:
      break;
  }
  if( node!=retNode ){
    Trace("sep-rewrite") << "Sep::rewrite : " << node << " -> " << retNode << std::endl;
  }
  return RewriteResponse(node==retNode ? REWRITE_DONE : REWRITE_AGAIN_FULL, retNode);
}

}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
