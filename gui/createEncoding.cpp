#include "createEncoding.hpp"
#include <stdio.h>

wxSizer* createEncoding(Encoding* encoding, wxWindow* parent, bool boxed) {
  switch (encoding->type) {
    case EncodingType::Bit: {
      wxSizer* sizer = new wxBoxSizer(wxHORIZONTAL);
      if (encoding->editable) {
        wxButton* button = new wxButton(parent, wxID_ANY, encoding->bit ? "1" : "0");
        button->Bind
          ( wxEVT_BUTTON
          , [encoding] (wxCommandEvent& event) {
              encoding->flipBit();
            }
          );
        sizer->Add(button, wxSizerFlags());
      } else {
        sizer->Add(new wxStaticText(parent, wxID_ANY, encoding->bit ? "1" : "0"), wxSizerFlags());
      }
      return sizer;
    }
    case EncodingType::Unit: {
      return new wxStaticBoxSizer(wxHORIZONTAL, parent);
    }
    case EncodingType::List: {
      wxSizer* sizer = boxed ? new wxStaticBoxSizer(wxHORIZONTAL, parent) : new wxBoxSizer(wxHORIZONTAL);
      for (int i = 0; i < encoding->numChildren; i++) {
        sizer->Add(createEncoding(encoding->childAt(i), parent, true), wxSizerFlags().Bottom().Border());
      }
      return sizer;
    }
    case EncodingType::NewType: {
      wxSizer* sizer = new wxStaticBoxSizer(wxHORIZONTAL, parent, encoding->ident);
      sizer->Add(createEncoding(encoding->childAt(0), parent, false), wxSizerFlags());
      return sizer;
    }
  }
}

void updateEncoding(wxSizer* sizer, Encoding* encoding) {
  switch (encoding->type) {
    case EncodingType::Bit: {
      if (encoding->editable) {
        dynamic_cast<wxButton*>(sizer->GetItem(static_cast<size_t>(0))->GetWindow())->SetLabel(encoding->bit ? "1" : "0");
      } else {
        dynamic_cast<wxStaticText*>(sizer->GetItem(static_cast<size_t>(0))->GetWindow())->SetLabel(encoding->bit ? "1" : "0");
      }
      break;
    }
    case EncodingType::Unit: break;
    case EncodingType::List:
    case EncodingType::NewType: {
      for (int i = 0; i < encoding->numChildren; i++) {
        updateEncoding(sizer->GetItem(i)->GetSizer(), encoding->childAt(i));
      }
      break;
    }
  }
}

