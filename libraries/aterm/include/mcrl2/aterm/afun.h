#ifndef AFUN_H
#define AFUN_H

#include <assert.h>
#include <string>
#include <cstdio>
#include <vector>
#include "mcrl2/aterm/atypes.h"
// #include "mcrl2/aterm/encoding.h"


namespace aterm
{

/* The AFun type */
class _SymEntry
{
  public:
    size_t header;
    size_t next;
    size_t reference_count;
    size_t id;
    char*  name;
    size_t count;  /* used in bafio.c */
    size_t index;  /* used in bafio.c */

    _SymEntry(const size_t h,const size_t i,size_t c,size_t in):
        header(h),
        next(size_t(-1)),
        reference_count(0),
        id(i),
        name(NULL),
        count(c),
        index(in)
    {}
};

void at_free_afun(const size_t n);

inline
bool AT_isValidAFun(const size_t sym);

class AFun
{
  protected:
    size_t m_number;

  public:
    static size_t first_free;
    static std::vector < _SymEntry* > &at_lookup_table()// As safio uses stable pointers to _SymEntries,
                                                       // we cannot use a vector of _SymEntry, as these
                                                       // are relocated. 
    {
      static std::vector < _SymEntry* > at_lookup_table;
      return at_lookup_table;
    }

    template <bool CHECK>
    static void increase_reference_count(const size_t n)
    {
      if (n!=size_t(-1))
      {
#ifdef PRINT_GC_INFO
fprintf(stderr,"increase afun reference count %ld (%ld, %s)\n",n,at_lookup_table()[n]->reference_count,at_lookup_table()[n]->name);
#endif
        assert(n<at_lookup_table().size());
        if (CHECK) assert(at_lookup_table()[n]->reference_count>0);
        at_lookup_table()[n]->reference_count++;
      }
    }

    static void decrease_reference_count(const size_t n)
    { 
      if (n!=size_t(-1))
      {
#ifdef PRINT_GC_INFO
fprintf(stderr,"decrease afun reference count %ld (%ld, %s)\n",n,at_lookup_table()[n]->reference_count,at_lookup_table()[n]->name);
#endif
        assert(n<at_lookup_table().size());
        assert(at_lookup_table()[n]->reference_count>0);

        if (--at_lookup_table()[n]->reference_count==0)
        {
          at_free_afun(n);
        }
      }
    }

  public:
    AFun():m_number(size_t(-1))
    {
    }

    AFun(const size_t n):m_number(n)
    {
      increase_reference_count<false>(m_number);
    }

    AFun(const AFun &f):m_number(f.m_number)
    {
      increase_reference_count<true>(m_number);
    }

    AFun &operator=(const AFun &f)
    {
      increase_reference_count<true>(f.m_number);
      decrease_reference_count(m_number); // Decrease after increasing the number, as otherwise this goes wrong when 
                                          // carrying out x=x;
      m_number=f.m_number;
      return *this;
    }

    ~AFun()
    {
      decrease_reference_count(m_number);
    }

    size_t number() const
    {
      assert(m_number==size_t(-1) || AT_isValidAFun(m_number));
      return m_number;
    }

    bool operator ==(const AFun &f) const
    {
      assert(m_number==size_t(-1) || AT_isValidAFun(m_number));
      assert(f.m_number==size_t(-1) || AT_isValidAFun(f.m_number));
      return m_number==f.m_number;
    }

    bool operator !=(const AFun &f) const
    {
      assert(m_number==size_t(-1) || AT_isValidAFun(m_number));
      assert(f.m_number==size_t(-1) || AT_isValidAFun(f.m_number));
      return m_number!=f.m_number;
    }

    bool operator <(const AFun &f) const
    {
      assert(m_number==size_t(-1) || AT_isValidAFun(m_number));
      assert(f.m_number==size_t(-1) || AT_isValidAFun(f.m_number));
      return m_number<f.m_number;
    }

    bool operator >(const AFun &f) const
    {
      assert(m_number==size_t(-1) || AT_isValidAFun(m_number));
      assert(f.m_number==size_t(-1) || AT_isValidAFun(f.m_number));
      return m_number>f.m_number;
    }

    bool operator <=(const AFun &f) const
    {
      assert(m_number==size_t(-1) || AT_isValidAFun(m_number));
      assert(f.m_number==size_t(-1) || AT_isValidAFun(f.m_number));
      return m_number<=f.m_number;
    }

    bool operator >=(const AFun &f) const
    {
      assert(m_number==size_t(-1) || AT_isValidAFun(m_number));
      assert(f.m_number==size_t(-1) || AT_isValidAFun(f.m_number));
      return m_number>=f.m_number;
    }
};


AFun ATmakeAFun(const char* name, const size_t arity, const bool quoted);

// The following afuns are used in bafio.

extern const AFun AS_INT;
extern const AFun AS_LIST;
extern const AFun AS_EMPTY_LIST;


inline
bool AT_isValidAFun(const size_t sym)
{
  return (sym != size_t(-1) && 
          sym < AFun::at_lookup_table().size() && 
          AFun::at_lookup_table()[sym]->reference_count>0);
}


// void AT_initAFun();
size_t AT_printAFun(const size_t sym, FILE* f);

/* inline
void AT_markAFun(const AFun &s)
{
  assert(s.number()<AFun::at_lookup_table.size());
  AFun::at_lookup_table[s.number()]->header |= MASK_MARK;
} */

/* inline
void AT_unmarkAFun(const AFun &s)
{
  assert(s.number()<AFun::at_lookup_table.size());
  AFun::at_lookup_table[s.number()]->header &= ~MASK_MARK;
} */

/* inline
bool AT_isMarkedAFun(const AFun &sym)
{
  assert(sym<AFun::at_lookup_table.size());
  return IS_MARKED(AFun::at_lookup_table[sym.number()]->header);
} */

/* void  AT_freeAFun(SymEntry sym);
void AT_markProtectedAFuns();
*/

size_t AT_hashAFun(const char* name, const size_t arity);
bool AT_findAFun(const char* name, const size_t arity, const bool quoted);
// void AT_unmarkAllAFuns();

std::string ATwriteAFunToString(const AFun &t);

}

#endif
