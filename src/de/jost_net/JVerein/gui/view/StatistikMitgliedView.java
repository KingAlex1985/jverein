/**********************************************************************
 * $Source$
 * $Revision$
 * $Date$
 * $Author$
 *
 * Copyright (c) by Heiner Jostkleigrewe
 * All rights reserved
 * heiner@jverein.de
 * www.jverein.de
 * $Log$
 * Revision 1.3  2007/12/21 11:28:06  jost
 * Mitgliederstatistik jetzt Stichtagsbezogen
 *
 * Revision 1.2  2007/02/23 20:27:42  jost
 * Mail- und Webadresse im Header korrigiert.
 *
 * Revision 1.1  2006/10/29 07:49:43  jost
 * Neu: Mitgliederstatistik
 *
 * Revision 1.1  2006/09/20 15:39:10  jost
 * *** empty log message ***
 *
 **********************************************************************/
package de.jost_net.JVerein.gui.view;

import de.jost_net.JVerein.gui.action.BackAction;
import de.jost_net.JVerein.gui.action.DokumentationAction;
import de.jost_net.JVerein.gui.control.MitgliedControl;
import de.willuhn.jameica.gui.AbstractView;
import de.willuhn.jameica.gui.GUI;
import de.willuhn.jameica.gui.util.ButtonArea;
import de.willuhn.jameica.gui.util.LabelGroup;
import de.willuhn.util.ApplicationException;

public class StatistikMitgliedView extends AbstractView
{
  public void bind() throws Exception
  {
    GUI.getView().setTitle("Mitgliederstatistik");

    final MitgliedControl control = new MitgliedControl(this);

    LabelGroup group = new LabelGroup(getParent(), "Parameter");
    group.addLabelPair("Stichtag", control.getStichtag());

    ButtonArea buttons = new ButtonArea(getParent(), 4);

    buttons.addButton("<< Zur�ck", new BackAction());
    buttons.addButton("Hilfe", new DokumentationAction(),
        DokumentationUtil.statistikmitglieder);
    buttons.addButton(control.getStartStatistikButton());
  }

  public void unbind() throws ApplicationException
  {
  }
}
