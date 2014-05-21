// A minimalistic BDD library, following Bryant's original paper
// and Andersen's lecture notes
//
// Written by Daniel Kroening on the 28th of September 2009
//
// see also http://www.cprover.org/miniBDD/

#ifndef _BDD_H_
#define _BDD_H_

#include <cassert>
#include <iostream>
#include <list>
#include <vector>
#include <map>
#include <string>

namespace bdd
{

class BDD
{
public:
  inline BDD();
  inline BDD(const BDD &x);
  inline ~BDD();

  // Boolean operators on BDDs
  BDD operator !() const;
  BDD operator ^(const BDD &) const;
  BDD operator ==(const BDD &) const;
  BDD operator &(const BDD &) const;
  BDD operator |(const BDD &) const;
  
  // copy operator
  inline BDD &operator=(const BDD &);
  
  friend class BDDManager;
  friend BDD apply(bool (*fkt)(bool x, bool y), const BDD &x, const BDD &y);
  
  inline bool is_constant() const;
  inline bool is_true() const;
  inline bool is_false() const;

  inline unsigned var() const;
  inline const BDD &low() const;
  inline const BDD &high() const;
  inline unsigned node_number() const;
  
  void clear();
  
protected:
  explicit inline BDD(class BDDnode *_node);
  class BDDnode *node;
};

class BDDnode
{
public:
  class BDDManager *mgr;
  unsigned var, node_number, reference_counter;
  BDD low, high;
  
  inline BDDnode(
    class BDDManager *_mgr,
    unsigned _var, unsigned _node_number,
    const BDD &_low, const BDD &_high);

  void inline add_reference();
  void remove_reference();
};

class BDDManager
{
public:
  BDDManager();
  ~BDDManager();

  BDD make_var(const std::string &label);

  inline const BDD &True();
  inline const BDD &False();
  
  friend class BDD;
  friend class BDDnode;
  
protected:
  typedef std::list<BDDnode> nodest;
  nodest nodes;
  BDD true_bdd, false_bdd;
  
  struct var_table_entryt
  {
    std::string label;
    inline var_table_entryt(const std::string &_label);
  };  

  typedef std::vector<var_table_entryt> var_tablet;
  var_tablet var_table;  
  
  // this is our reverse-map for nodes
  struct reverse_keyt
  {
    unsigned var, low, high;
    inline reverse_keyt(
      unsigned _var, const BDD &_low, const BDD &_high);
  };
  
  typedef std::map<reverse_keyt, BDDnode *> reverse_mapt;
  reverse_mapt reverse_map;
  
  friend bool operator < (const reverse_keyt &x, const reverse_keyt &y);

  // create a node (consulting the reverse-map)
  BDD mk(unsigned var, const BDD &low, const BDD &high);

  friend BDD apply(bool (*fkt)(bool x, bool y), const BDD &x, const BDD &y);

private:
  void append_node(
    unsigned var, unsigned node_number,
    const BDD &low, const BDD &high)
  {
    nodes.emplace_back(this, var, node_number, low, high);
  }
};

BDD apply(bool (*fkt)(bool x, bool y), const BDD &x, const BDD &y);

#define forall_nodes(it) for(nodest::const_iterator it=nodes.begin(); \
  it!=nodes.end(); it++)

// inline functions

BDD::BDD():node(nullptr)
{
}

BDD::BDD(const BDD &x):node(x.node)
{
  if(node!=nullptr) node->add_reference();
}

BDD::BDD(BDDnode *_node):node(_node)
{
  if(node!=nullptr) node->add_reference();
}

BDD &BDD::operator=(const BDD &x)
{
  assert(&x!=this);
  clear();

  node=x.node;

  if(node!=nullptr) node->add_reference();

  return *this;
}

BDD::~BDD()
{
  clear();
}

bool BDD::is_constant() const
{
  assert(node!=nullptr);
  return node->node_number<=1;
}

bool BDD::is_true() const
{
  assert(node!=nullptr);
  return node->node_number==1;
}

bool BDD::is_false() const
{
  assert(node!=nullptr);
  return node->node_number==0;
}

unsigned BDD::var() const
{
  assert(node!=nullptr);
  return node->var;
}

unsigned BDD::node_number() const
{
  assert(node!=nullptr);
  return node->node_number;
}

const BDD &BDD::low() const
{
  assert(node!=nullptr);
  assert(node->node_number>=2);
  return node->low;
}

const BDD &BDD::high() const
{
  assert(node!=nullptr);
  assert(node->node_number>=2);
  return node->high;
}

BDDnode::BDDnode(
  BDDManager *_mgr,
  unsigned _var, unsigned _node_number,
  const BDD &_low, const BDD &_high):
  mgr(_mgr), var(_var), node_number(_node_number),
  low(_low), high(_high),
  reference_counter(0)
{
}

BDDManager::var_table_entryt::var_table_entryt(
  const std::string &_label):label(_label)
{
}

const BDD &BDDManager::True()
{
  return true_bdd;
}

const BDD &BDDManager::False()
{
  return false_bdd;
}

void BDDnode::add_reference()
{
  reference_counter++;
}
  
BDDManager::reverse_keyt::reverse_keyt(
  unsigned _var, const BDD &_low, const BDD &_high):
  var(_var), low(_low.node->node_number), high(_high.node->node_number)
{
}

}

#endif

