#ifndef ENCODING_H
#define ENCODING_H

#include <wx/wxprec.h>
#ifndef WX_PRECOMP
#include <wx/wx.h>
#endif

#include <string>

template <typename T>
T* dup(size_t n, const T* p) {
  T* q = new T[n];
  memcpy(q, p, n * sizeof(T));
  return q;
}

enum class EncodingType : char {
  Bit, Unit, List, NewType
};

struct Encoding {
  int numDescendants;
  const EncodingType* types;
  const char* numChildren;
  const char* idents;
  const char* indexToIdent;
  char* bits;
  const char* children;
  int editable;
  void (*flipBitAt)(const char*);
  wxControl** bitWidgets;
};

extern "C"
Encoding* mkEncoding
  ( int numDescendants
  , const EncodingType* types
  , const char* numChildren
  , int lenIdents
  , const char* idents
  , const char* indexToIdent
  , char* bits
  , const char* children
  , int editable
  , void (*flipBitAt)(const char*)
  );

wxSizer* createEncoding(Encoding* encoding, wxWindow* parent, int i = 0, std::string index = "");
void updateEncoding(Encoding* encoding);

#endif
