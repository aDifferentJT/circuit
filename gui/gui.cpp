#include "gui.h"

// wxWidgets "Hello world" Program
// For compilers that support precompilation, includes "wx/wx.h".
#include <wx/wxprec.h>
#ifndef WX_PRECOMP
    #include <wx/wx.h>
#endif

#include "createEncoding.hpp"

Encoding* input = nullptr;
Encoding* output = nullptr;

class MyFrame : public wxFrame {
public:
    MyFrame(const wxString& title, const wxPoint& pos, const wxSize& size);

    wxSizer* topSizer;
private:
    void OnExit(wxCommandEvent& event);
    void OnAbout(wxCommandEvent& event);
    wxDECLARE_EVENT_TABLE();
};

class MyApp : public wxApp {
public:
    virtual bool OnInit();

    MyFrame* frame;
};

wxBEGIN_EVENT_TABLE(MyFrame, wxFrame)
    EVT_MENU(wxID_EXIT,  MyFrame::OnExit)
    EVT_MENU(wxID_ABOUT, MyFrame::OnAbout)
wxEND_EVENT_TABLE()

wxIMPLEMENT_APP_NO_MAIN(MyApp);

bool MyApp::OnInit() {
    frame = new MyFrame("", wxPoint(50, 50), wxSize(450, 340));
    frame->Show( true );
    return true;
}

MyFrame::MyFrame(const wxString& title, const wxPoint& pos, const wxSize& size)
  : wxFrame(NULL, wxID_ANY, title, pos, size)
  {
    wxMenu *menuFile = new wxMenu;
    menuFile->Append(wxID_EXIT);

    wxMenu *menuHelp = new wxMenu;
    menuHelp->Append(wxID_ABOUT);

    wxMenuBar *menuBar = new wxMenuBar;
    menuBar->Append(menuFile, "&File");
    menuBar->Append(menuHelp, "&Help");
    SetMenuBar(menuBar);

    CreateStatusBar();
    SetStatusText("Welcome to wxWidgets!");

    topSizer = new wxBoxSizer( wxVERTICAL );
    topSizer->Add(createEncoding(output, this), wxSizerFlags().Center());
    topSizer->Add(createEncoding(input, this), wxSizerFlags().Center());
    SetSizerAndFit(topSizer);
}

void MyFrame::OnExit(wxCommandEvent& event) {
    Close(true);
}

void MyFrame::OnAbout(wxCommandEvent& event) {
    wxMessageBox
      ( "This is a wxWidgets' Hello world sample"
      , "About Hello World", wxOK | wxICON_INFORMATION
      );
}

void gui(Encoding* _input, Encoding* _output) {
  delete input;
  input = _input;
  delete output;
  output = _output;

  static bool isInitialised = false;
  if (isInitialised) {
    updateEncoding(wxGetApp().frame->topSizer->GetItem(static_cast<size_t>(0))->GetSizer(), output);
    updateEncoding(wxGetApp().frame->topSizer->GetItem(static_cast<size_t>(1))->GetSizer(), input);
  } else {
    isInitialised = true;
    int argc = 0;
    char* argv[0]{};
    wxEntry(argc, argv);
  }
}

