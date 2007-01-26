#ifndef MARKSTATERULEDIALOG_H
#define MARKSTATERULEDIALOG_H
#include <map>
#include <wx/wx.h>
#include <wx/checklst.h>
#include "mediator.h"
#include "aterm2.h"
#include "utils.h"

class MarkStateRuleDialog : public wxDialog { 
  public:
    MarkStateRuleDialog(wxWindow* parent,Mediator* owner,ATermList svspec);
    ~MarkStateRuleDialog();
    void      onParameterChoice(wxCommandEvent& event);
    Utils::MarkRule* getMarkRule();
    wxString  getMarkRuleString();
    void      setMarkRule(Utils::MarkRule* mr,ATermList svspec);
  private:
    Mediator*			mediator;
    std::map< wxString, int >	parameterIndices;
    wxListBox*			parameterListBox;
    std::map< wxString, ATermAppl >	parameterTypes;
    wxListBox*			relationListBox;
    std::map< wxString, int >	valueIndices;
    wxCheckListBox*		valuesListBox;

    void loadValues(wxString paramName);

    DECLARE_EVENT_TABLE();
};

#endif
