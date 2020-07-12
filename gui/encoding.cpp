#include "encoding.hpp"
#include <stdio.h>

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
  ) {
  Encoding* encoding = new Encoding
    { numDescendants
    , dup(numDescendants, types)
    , dup(numDescendants, numChildren)
    , dup(lenIdents, idents)
    , dup(numDescendants, indexToIdent)
    , dup(numDescendants, bits)
    , dup(numDescendants, children)
    , editable
    , flipBitAt
    , new wxControl*[numDescendants]
    };
  for (int i = 0; i < numDescendants; i++) {
    encoding->bitWidgets[i] = nullptr;
  }
  return encoding;
}

wxSizer* createEncoding(Encoding* encoding, wxWindow* parent, int i, std::string index) {
  switch (encoding->types[i]) {
    case EncodingType::Bit: {
      wxSizer* sizer = new wxBoxSizer(wxHORIZONTAL);
      if (encoding->editable) {
        encoding->bitWidgets[i] = new wxButton(parent, -1, encoding->bits[i] ? "1" : "0");
        encoding->bitWidgets[i]->Bind
          ( wxEVT_BUTTON
          , [encoding, index] (wxCommandEvent& event) {
              encoding->flipBitAt(index.c_str());
            }
          );
      } else {
        encoding->bitWidgets[i] = new wxStaticText(parent, -1, encoding->bits[i] ? "1" : "0");
      }
      sizer->Add(encoding->bitWidgets[i], wxSizerFlags());
      return sizer;
    }
    case EncodingType::Unit: {
      return new wxStaticBoxSizer(wxHORIZONTAL, parent);
    }
    case EncodingType::List: {
      wxSizer* sizer = new wxStaticBoxSizer(wxHORIZONTAL, parent);
      for (int j = 0; j < encoding->numChildren[i]; j++) {
        char* j_string = new char[2];
        j_string[0] = static_cast<char>(j) + 1;
        j_string[1] = '\0';
        sizer->Add(createEncoding(encoding, parent, encoding->children[i] + j, index + j_string), wxSizerFlags());
      }
      return sizer;
    }
    case EncodingType::NewType: {
      wxSizer* sizer = new wxStaticBoxSizer(wxHORIZONTAL, parent, encoding->idents + encoding->indexToIdent[i]);
      sizer->Add(createEncoding(encoding, parent, encoding->children[i], index), wxSizerFlags());
      return sizer;
    }
  }
}

void updateEncoding(Encoding* encoding) {
  for (int i = 0; i < encoding->numDescendants; i++) {
    if (encoding->bitWidgets[i]) {
      encoding->bitWidgets[i]->SetLabel(encoding->bits[i] ? "1" : "0");
    }
  }
}

